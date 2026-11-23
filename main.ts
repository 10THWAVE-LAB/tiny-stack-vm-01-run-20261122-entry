// Tiny stack VM (make.fun tiny-stack-vm-01). Runs every bytecode program in
// the input set; writes each program's output bytes + exit code. Deterministic:
// no clock, no randomness, no environment-dependent behaviour.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcodes in order; META holds [immediate bytes, pops, pushes] as 3 digits
// per opcode, in the same order.
const OPS = [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 48, 49, 50, 51, 52, 64, 65, 80, 81, 82, 83];
const META = '000101401010012022023033021021021021021021021011021021021011021021021021021021200210210200000011020010010001010';
const IMM = new Int8Array(256).fill(-1);
const POPS = new Int8Array(256);
const PUSHES = new Int8Array(256);
OPS.forEach((o, i) => { IMM[o] = META[i * 3] - 0; POPS[o] = META[i * 3 + 1] - 0; PUSHES[o] = META[i * 3 + 2] - 0; });

// Runs one program on its input bytes; returns [output, exit code].
// A trap ends the run at once with the trap code; output so far is kept.
function run(p, q) {
  const n = p.length;
  const d = new Int32Array(256);
  const c = new Int32Array(64);
  const m = new Int32Array(256);
  const o = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (e) => [o.subarray(0, ol), e];
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    const im = IMM[op];
    if (im < 0) return done(5);
    if (pc + im >= n) return done(9);
    if (sp < POPS[op]) return done(2);
    if (sp - POPS[op] + PUSHES[op] > 256) return done(3);
    steps++;
    pc += 1 + im;
    switch (op) {
      case 0: return done(0); // HALT
      case 1: d[sp++] = (p[pc - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: d[sp++] = p[pc - 4] | (p[pc - 3] << 8) | (p[pc - 2] << 16) | (p[pc - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: d[sp] = d[sp - 1]; sp++; break; // DUP
      case 5: { const t = d[sp - 1]; d[sp - 1] = d[sp - 2]; d[sp - 2] = t; break; } // SWAP
      case 6: d[sp] = d[sp - 2]; sp++; break; // OVER
      case 7: { const t = d[sp - 3]; d[sp - 3] = d[sp - 2]; d[sp - 2] = d[sp - 1]; d[sp - 1] = t; break; } // ROT
      case 23: d[sp - 1] = -d[sp - 1] | 0; break; // NEG, wraps
      case 27: d[sp - 1] = ~d[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = d[--sp];
        const a = d[sp - 1];
        let r;
        if (op === 16) r = (a + b) | 0; // ADD
        else if (op === 17) r = (a - b) | 0; // SUB
        else if (op === 18) r = Math.imul(a, b); // MUL, low 32 bits exactly
        else if (op === 19) { // DIV, truncates toward zero
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) { // MOD, sign of a
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) { // DIVU
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) { // MODU
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        }
        else if (op === 24) r = a & b; // AND
        else if (op === 25) r = a | b; // OR
        else if (op === 26) r = a ^ b; // XOR
        else if (op === 28) r = a << (b & 31); // SHL
        else if (op === 29) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 30) r = a >>> (b & 31); // SHRU, logical
        else if (op === 32) r = a === b ? 1 : 0; // EQ
        else if (op === 33) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        d[sp - 1] = r;
        break;
      }
      case 48: case 49: case 50: { // JMP / JZ / JNZ, signed 2-byte offset
        const rel = ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
        if (op === 48) pc += rel;
        else if ((op === 49) === (d[--sp] === 0)) pc += rel;
        break;
      }
      case 51: // CALL, 2-byte unsigned address
        if (cp === 64) return done(7);
        c[cp++] = pc;
        pc = p[pc - 2] | (p[pc - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return done(8);
        pc = c[--cp];
        break;
      case 64: { // LOAD
        const a = d[sp - 1];
        if (a < 0 || a > 255) return done(6);
        d[sp - 1] = m[a];
        break;
      }
      case 65: { // STORE: (value address --)
        const a = d[sp - 1];
        if (a < 0 || a > 255) return done(6);
        sp -= 2;
        m[a] = d[sp];
        break;
      }
      case 80: { // PRINT: decimal ASCII, no newline; over the cap writes nothing
        const s = String(d[sp - 1]);
        if (ol + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) o[ol++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte
        if (ol + 1 > 65536) return done(11);
        o[ol++] = d[--sp] & 255;
        break;
      case 82: d[sp++] = ip < q.length ? q[ip++] : -1; break; // IN: -1 when used up
      case 83: return done(d[--sp] & 255); // EXIT: low byte is the code
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  if (!existsSync(join(dir, 'program.bin'))) continue;
  const p = readFileSync(join(dir, 'program.bin'));
  const q = existsSync(join(dir, 'input.bin')) ? readFileSync(join(dir, 'input.bin')) : Buffer.alloc(0);
  let out = Buffer.alloc(0);
  let exit = 0;
  try {
    [out, exit] = run(p, q);
  } catch {
    out = Buffer.alloc(0); // one bad instance must not take down the other 39
    exit = 0;
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), exit + '\n');
}
