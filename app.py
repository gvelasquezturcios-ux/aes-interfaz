import hashlib
import os
import gradio as gr

def multiplicar_en_campo(a, b):
    res = 0
    for _ in range(8):
        if b & 1:
            res ^= a
        carry = a & 0x80
        a = (a << 1) & 0xFF
        if carry:
            a ^= 0x1B
        b >>= 1
    return res

def division_polinomios(a, b):
    q, r = 0, a
    grado_b = b.bit_length() - 1
    while r.bit_length() - 1 >= grado_b and r != 0:
        d = (r.bit_length() - 1) - grado_b
        q ^= 1 << d
        r ^= b << d
    return q, r

def multiplicar_polinomios(a, b):
    res = 0
    while b:
        if b & 1:
            res ^= a
        a <<= 1
        b >>= 1
    return res

def inverso_en_campo(a):
    if a == 0:
        return 0
    r0, r1 = 0x11B, a
    s0, s1 = 0, 1
    while r1 != 0:
        q, r = division_polinomios(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 ^ multiplicar_polinomios(q, s1)
    return s0

def rotar_bits_izquierda(b, n):
    return ((b << n) | (b >> (8 - n))) & 0xFF

def construir_sbox():
    sbox = [0] * 256
    for b in range(256):
        inv = inverso_en_campo(b)
        sbox[b] = (inv ^ rotar_bits_izquierda(inv, 1) ^ rotar_bits_izquierda(inv, 2)
                   ^ rotar_bits_izquierda(inv, 3) ^ rotar_bits_izquierda(inv, 4) ^ 0x63)
    return sbox

def construir_sbox_inversa(sbox):
    inv = [0] * 256
    for i, v in enumerate(sbox):
        inv[v] = i
    return inv

SBOX = construir_sbox()
SBOX_INV = construir_sbox_inversa(SBOX)

def sub_bytes(estado):
    return [[SBOX[estado[f][c]] for c in range(4)] for f in range(4)]

def inv_sub_bytes(estado):
    return [[SBOX_INV[estado[f][c]] for c in range(4)] for f in range(4)]

def shift_rows(estado):
    return [[estado[f][(c + f) % 4] for c in range(4)] for f in range(4)]

def inv_shift_rows(estado):
    return [[estado[f][(c - f) % 4] for c in range(4)] for f in range(4)]

def mix_columns(estado):
    nuevo = [[0]*4 for _ in range(4)]
    for c in range(4):
        a = [estado[f][c] for f in range(4)]
        nuevo[0][c] = multiplicar_en_campo(a[0], 2) ^ multiplicar_en_campo(a[1], 3) ^ a[2] ^ a[3]
        nuevo[1][c] = a[0] ^ multiplicar_en_campo(a[1], 2) ^ multiplicar_en_campo(a[2], 3) ^ a[3]
        nuevo[2][c] = a[0] ^ a[1] ^ multiplicar_en_campo(a[2], 2) ^ multiplicar_en_campo(a[3], 3)
        nuevo[3][c] = multiplicar_en_campo(a[0], 3) ^ a[1] ^ a[2] ^ multiplicar_en_campo(a[3], 2)
    return nuevo

def inv_mix_columns(estado):
    nuevo = [[0]*4 for _ in range(4)]
    for c in range(4):
        a = [estado[f][c] for f in range(4)]
        nuevo[0][c] = (multiplicar_en_campo(a[0], 14) ^ multiplicar_en_campo(a[1], 11)
                       ^ multiplicar_en_campo(a[2], 13) ^ multiplicar_en_campo(a[3], 9))
        nuevo[1][c] = (multiplicar_en_campo(a[0], 9) ^ multiplicar_en_campo(a[1], 14)
                       ^ multiplicar_en_campo(a[2], 11) ^ multiplicar_en_campo(a[3], 13))
        nuevo[2][c] = (multiplicar_en_campo(a[0], 13) ^ multiplicar_en_campo(a[1], 9)
                       ^ multiplicar_en_campo(a[2], 14) ^ multiplicar_en_campo(a[3], 11))
        nuevo[3][c] = (multiplicar_en_campo(a[0], 11) ^ multiplicar_en_campo(a[1], 13)
                       ^ multiplicar_en_campo(a[2], 9) ^ multiplicar_en_campo(a[3], 14))
    return nuevo

def add_round_key(estado, clave_ronda):
    return [[estado[f][c] ^ clave_ronda[f][c] for c in range(4)] for f in range(4)]

def expandir_clave(clave, nk):
    nr = {4: 10, 6: 12, 8: 14}[nk]
    palabras = [list(clave[i:i+4]) for i in range(0, len(clave), 4)]
    rcon = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]
    total = 4 * (nr + 1)
    for i in range(nk, total):
        temp = palabras[i-1].copy()
        if i % nk == 0:
            temp = temp[1:] + temp[:1]
            temp = [SBOX[b] for b in temp]
            temp[0] ^= rcon[i//nk - 1]
        elif nk > 6 and i % nk == 4:
            temp = [SBOX[b] for b in temp]
        palabras.append([palabras[i-nk][j] ^ temp[j] for j in range(4)])
    return [palabras[4*i:4*i+4] for i in range(nr + 1)], nr

def clave_a_estado(clave):
    return [[clave[f + 4*c] for c in range(4)] for f in range(4)]

def estado_a_matriz(palabras):
    return [[palabras[c][f] for c in range(4)] for f in range(4)]

def matriz_a_bytes(estado):
    return bytes([estado[f][c] for c in range(4) for f in range(4)])

def rellenar(datos, bloque=16):
    falta = bloque - (len(datos) % bloque)
    return datos + bytes([falta] * falta)

def verificar_relleno(datos):
    if not datos:
        return False
    ultimo = datos[-1]
    if ultimo < 1 or ultimo > 16:
        return False
    if len(datos) < ultimo:
        return False
    return all(b == ultimo for b in datos[-ultimo:])

def quitar_relleno(datos):
    return datos[:-datos[-1]]

def cifrar_bloque(bloque, subclaves, nr):
    estado = clave_a_estado(bloque)
    estado = add_round_key(estado, estado_a_matriz(subclaves[0]))
    for ronda in range(1, nr):
        estado = sub_bytes(estado)
        estado = shift_rows(estado)
        estado = mix_columns(estado)
        estado = add_round_key(estado, estado_a_matriz(subclaves[ronda]))
    estado = sub_bytes(estado)
    estado = shift_rows(estado)
    estado = add_round_key(estado, estado_a_matriz(subclaves[nr]))
    return matriz_a_bytes(estado)

def descifrar_bloque(bloque, subclaves, nr):
    estado = clave_a_estado(bloque)
    estado = add_round_key(estado, estado_a_matriz(subclaves[nr]))
    for ronda in range(nr - 1, 0, -1):
        estado = inv_shift_rows(estado)
        estado = inv_sub_bytes(estado)
        estado = add_round_key(estado, estado_a_matriz(subclaves[ronda]))
        estado = inv_mix_columns(estado)
    estado = inv_shift_rows(estado)
    estado = inv_sub_bytes(estado)
    estado = add_round_key(estado, estado_a_matriz(subclaves[0]))
    return matriz_a_bytes(estado)

def cifrar(mensaje, clave, nk):
    subclaves, nr = expandir_clave(clave, nk)
    datos = rellenar(mensaje)
    return b"".join(cifrar_bloque(datos[i:i+16], subclaves, nr)
                    for i in range(0, len(datos), 16))

def descifrar(cifrado, clave, nk):
    subclaves, nr = expandir_clave(clave, nk)
    datos = b"".join(descifrar_bloque(cifrado[i:i+16], subclaves, nr)
                     for i in range(0, len(cifrado), 16))
    if not verificar_relleno(datos):
        raise ValueError("La contraseña es incorrecta o el mensaje fue alterado.")
    return quitar_relleno(datos)

def verificar_nist():
    vectores = [
        (4, "AES-128", "000102030405060708090A0B0C0D0E0F", "69C4E0D86A7B0430D8CDB78070B4C55A"),
        (6, "AES-192", "000102030405060708090A0B0C0D0E0F1011121314151617", "DDA97CA4864CDFE06EAF70A0EC0D7191"),
        (8, "AES-256", "000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F", "8EA2B7CA516745BFEAFC49904B496089"),
    ]
    texto = bytes.fromhex("00112233445566778899AABBCCDDEEFF")
    todos_ok = True
    for nk, nombre, clave_hex, esperado in vectores:
        clave = bytes.fromhex(clave_hex)
        subclaves, nr = expandir_clave(clave, nk)
        obtenido = cifrar_bloque(texto, subclaves, nr).hex().upper()
        if obtenido == esperado:
            print(f"✅ {nombre}: {obtenido}")
        else:
            print(f"❌ {nombre}: se esperaba {esperado}, se obtuvo {obtenido}")
            todos_ok = False
    return todos_ok

def mostrar_subclaves(subclaves):
    lineas = []
    for i, palabras in enumerate(subclaves):
        palabras_hex = " ".join("".join(f"{b:02X}" for b in palabra) for palabra in palabras)
        lineas.append(f"  Subclave {i:2d}: {palabras_hex}")
    return "\n".join(lineas)

def mostrar_sbox_byte_a_byte(estado_antes, estado_despues):
    lineas = []
    for f in range(4):
        for c in range(4):
            lineas.append(f"    [{f},{c}] {estado_antes[f][c]:02X} → {estado_despues[f][c]:02X}")
    return "\n".join(lineas)

def proceso_cifrado(mensaje_bytes, bloque, subclaves, nr, clave):
    lineas = []
    lineas.append("=" * 60)
    lineas.append("CONVERSIÓN DEL MENSAJE A HEXADECIMAL")
    lineas.append("=" * 60)
    lineas.append(f"Texto original: {mensaje_bytes.decode('utf-8', errors='replace')}")
    lineas.append(f"Bytes (hex): {mensaje_bytes.hex().upper()}")
    lineas.append(f"Longitud: {len(mensaje_bytes)} bytes")
    relleno_bytes = rellenar(mensaje_bytes)
    lineas.append(f"Con relleno PKCS#7: {relleno_bytes.hex().upper()}")
    lineas.append(f"Longitud con relleno: {len(relleno_bytes)} bytes")

    lineas.append("\n" + "=" * 60)
    lineas.append("CLAVE DERIVADA Y EXPANSIÓN DE CLAVE")
    lineas.append("=" * 60)
    lineas.append(f"Clave derivada (hex): {clave.hex().upper()}")
    lineas.append(f"Número de subclaves: {len(subclaves)}")
    lineas.append(mostrar_subclaves(subclaves))

    lineas.append("\n" + "=" * 60)
    lineas.append("PROCESO PASO A PASO DEL CIFRADO (PRIMER BLOQUE)")
    lineas.append("=" * 60)
    lineas.append(f"Primer bloque (hex): {bloque.hex().upper()}")
    lineas.append(f"Variante: {nr} rondas")

    estado = clave_a_estado(bloque)
    lineas.append("\nEstado inicial (matriz 4x4, por columnas):")
    for fila in estado:
        lineas.append("  " + " ".join(f"{b:02X}" for b in fila))

    estado = add_round_key(estado, estado_a_matriz(subclaves[0]))
    lineas.append("\nTras AddRoundKey inicial:")
    for fila in estado:
        lineas.append("  " + " ".join(f"{b:02X}" for b in fila))

    for ronda in range(1, nr):
        lineas.append(f"\n--- RONDA {ronda} ---")
        estado_antes = [fila[:] for fila in estado]
        estado = sub_bytes(estado)
        lineas.append("  Tras SubBytes:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
        if ronda == 1:
            lineas.append("  S-Box aplicada byte a byte (primera ronda):")
            lineas.append(mostrar_sbox_byte_a_byte(estado_antes, estado))
        estado = shift_rows(estado)
        lineas.append("  Tras ShiftRows:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
        estado = mix_columns(estado)
        lineas.append("  Tras MixColumns:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
        estado = add_round_key(estado, estado_a_matriz(subclaves[ronda]))
        lineas.append("  Tras AddRoundKey:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))

    lineas.append(f"\n--- RONDA FINAL ({nr}) ---")
    estado = sub_bytes(estado)
    lineas.append("  Tras SubBytes:")
    for fila in estado:
        lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
    estado = shift_rows(estado)
    lineas.append("  Tras ShiftRows:")
    for fila in estado:
        lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
    estado = add_round_key(estado, estado_a_matriz(subclaves[nr]))
    lineas.append("  Tras AddRoundKey:")
    for fila in estado:
        lineas.append("    " + " ".join(f"{b:02X}" for b in fila))

    cifrado_bytes = matriz_a_bytes(estado)
    lineas.append("\n" + "=" * 60)
    lineas.append("CONVERSIÓN DEL ESTADO A HEXADECIMAL")
    lineas.append("=" * 60)
    lineas.append("Estado final (matriz):")
    for fila in estado:
        lineas.append("  " + " ".join(f"{b:02X}" for b in fila))
    lineas.append(f"\nBytes del bloque cifrado (hex): {cifrado_bytes.hex().upper()}")

    return "\n".join(lineas)

def proceso_descifrado(cifrado_bytes, bloque, subclaves, nr, clave):
    lineas = []
    lineas.append("=" * 60)
    lineas.append("CONVERSIÓN DEL MENSAJE CIFRADO A HEXADECIMAL")
    lineas.append("=" * 60)
    lineas.append(f"Bytes (hex): {cifrado_bytes.hex().upper()}")
    lineas.append(f"Longitud: {len(cifrado_bytes)} bytes")

    lineas.append("\n" + "=" * 60)
    lineas.append("CLAVE DERIVADA Y EXPANSIÓN DE CLAVE")
    lineas.append("=" * 60)
    lineas.append(f"Clave derivada (hex): {clave.hex().upper()}")
    lineas.append(f"Número de subclaves: {len(subclaves)}")
    lineas.append(mostrar_subclaves(subclaves))

    lineas.append("\n" + "=" * 60)
    lineas.append("PROCESO PASO A PASO DEL DESCIFRADO (PRIMER BLOQUE)")
    lineas.append("=" * 60)
    lineas.append(f"Primer bloque cifrado (hex): {bloque.hex().upper()}")
    lineas.append(f"Variante: {nr} rondas")

    estado = clave_a_estado(bloque)
    lineas.append("\nEstado inicial (matriz 4x4, por columnas):")
    for fila in estado:
        lineas.append("  " + " ".join(f"{b:02X}" for b in fila))

    estado = add_round_key(estado, estado_a_matriz(subclaves[nr]))
    lineas.append(f"\nTras AddRoundKey con la subclave {nr} (ronda final del cifrado):")
    for fila in estado:
        lineas.append("  " + " ".join(f"{b:02X}" for b in fila))

    for ronda in range(nr - 1, 0, -1):
        lineas.append(f"\n--- RONDA INVERSA {nr - ronda} (ronda {ronda} original) ---")
        estado = inv_shift_rows(estado)
        lineas.append("  Tras InvShiftRows:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
        estado_antes = [fila[:] for fila in estado]
        estado = inv_sub_bytes(estado)
        lineas.append("  Tras InvSubBytes:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
        if ronda == nr - 1:
            lineas.append("  S-Box inversa aplicada byte a byte (primera ronda inversa):")
            lineas.append(mostrar_sbox_byte_a_byte(estado_antes, estado))
        estado = add_round_key(estado, estado_a_matriz(subclaves[ronda]))
        lineas.append("  Tras AddRoundKey:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
        estado = inv_mix_columns(estado)
        lineas.append("  Tras InvMixColumns:")
        for fila in estado:
            lineas.append("    " + " ".join(f"{b:02X}" for b in fila))

    lineas.append("\n--- RONDA FINAL INVERSA ---")
    estado = inv_shift_rows(estado)
    lineas.append("  Tras InvShiftRows:")
    for fila in estado:
        lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
    estado = inv_sub_bytes(estado)
    lineas.append("  Tras InvSubBytes:")
    for fila in estado:
        lineas.append("    " + " ".join(f"{b:02X}" for b in fila))
    estado = add_round_key(estado, estado_a_matriz(subclaves[0]))
    lineas.append("  Tras AddRoundKey:")
    for fila in estado:
        lineas.append("    " + " ".join(f"{b:02X}" for b in fila))

    descifrado_bytes = matriz_a_bytes(estado)
    lineas.append("\n" + "=" * 60)
    lineas.append("CONVERSIÓN DEL ESTADO A HEXADECIMAL Y TEXTO")
    lineas.append("=" * 60)
    lineas.append("Estado final (matriz):")
    for fila in estado:
        lineas.append("  " + " ".join(f"{b:02X}" for b in fila))
    lineas.append(f"\nBytes del bloque descifrado (hex): {descifrado_bytes.hex().upper()}")
    lineas.append(f"Texto del bloque descifrado: {descifrado_bytes.decode('utf-8', errors='replace')}")

    return "\n".join(lineas)

estado_actual = {"accion": None, "mensaje": None, "cifrado": None, "contrasena": None, "variante": None}

def ejecutar(accion, mensaje, contrasena, variante):
    if not mensaje or not contrasena:
        return "Escribe un mensaje y una contraseña.", ""

    nk = {"AES-128": 4, "AES-192": 6, "AES-256": 8}[variante]
    clave = hashlib.sha256(contrasena.encode()).digest()[:nk*4]

    if accion == "cifrar":
        resultado = cifrar(mensaje.encode(), clave, nk)
        salida = resultado.hex().upper()
        estado_actual.update({"accion": "cifrar", "mensaje": mensaje, "cifrado": resultado,
                              "contrasena": contrasena, "variante": variante})
        return salida, ""
    else:
        try:
            cifrado = bytes.fromhex(mensaje.strip().replace(" ", ""))
            descifrado = descifrar(cifrado, clave, nk)
            salida = descifrado.decode("utf-8")
            estado_actual.update({"accion": "descifrar", "mensaje": mensaje, "cifrado": cifrado,
                                  "contrasena": contrasena, "variante": variante})
            return salida, ""
        except Exception:
            return "❌ Error: contraseña incorrecta o mensaje alterado.", ""

def ver_proceso():
    if estado_actual["accion"] is None:
        return "Primero cifra o descifra un mensaje para poder ver el proceso."

    nk = {"AES-128": 4, "AES-192": 6, "AES-256": 8}[estado_actual["variante"]]
    clave = hashlib.sha256(estado_actual["contrasena"].encode()).digest()[:nk*4]
    subclaves, nr = expandir_clave(clave, nk)

    if estado_actual["accion"] == "cifrar":
        datos = rellenar(estado_actual["mensaje"].encode())
        return proceso_cifrado(estado_actual["mensaje"].encode(), datos[:16], subclaves, nr, clave)
    else:
        cifrado = estado_actual["cifrado"]
        return proceso_descifrado(cifrado, cifrado[:16], subclaves, nr, clave)

print("\nVerificando implementación contra vectores del NIST...")
if verificar_nist():
    print("\n✅ Implementación verificada.\n")
else:
    print("\n❌ Error en la verificación. Revisa el código.\n")

with gr.Blocks(title="AES") as demo:
    gr.Markdown("# AES\nCifra, descifra y visualiza el proceso paso a paso.")

    variante = gr.Radio(["AES-128", "AES-192", "AES-256"], value="AES-128", label="Variante")

    with gr.Row():
        with gr.Column():
            mensaje = gr.Textbox(label="Mensaje (texto para cifrar, hex para descifrar)", lines=4)
            contrasena = gr.Textbox(label="Contraseña", type="password")

            with gr.Row():
                boton_cifrar = gr.Button("Cifrar", variant="primary")
                boton_descifrar = gr.Button("Descifrar")
                boton_proceso = gr.Button("Ver proceso")

        with gr.Column():
            salida = gr.Textbox(label="Resultado", lines=4)
            proceso = gr.Textbox(label="Proceso paso a paso", lines=50)

    boton_cifrar.click(
        lambda m, c, v: ejecutar("cifrar", m, c, v),
        [mensaje, contrasena, variante],
        [salida, proceso]
    )

    boton_descifrar.click(
        lambda m, c, v: ejecutar("descifrar", m, c, v),
        [mensaje, contrasena, variante],
        [salida, proceso]
    )

    boton_proceso.click(
        ver_proceso,
        [],
        [proceso]
    )

    contrasena.submit(
        lambda m, c, v: ejecutar("cifrar", m, c, v),
        [mensaje, contrasena, variante],
        [salida, proceso]
    )

demo.launch(server_name="0.0.0.0", server_port=int(os.environ.get("PORT", 7860)))
