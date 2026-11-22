// Tiny stack VM (ISA v1): runs every program.bin on its input.bin and writes
// stdout.bin + exit.txt per instance. 32-bit wrapping ints, a 256-value stack,
// a 64-deep call stack, 256 words of memory. A trap keeps the output written
// before it and exits with the trap's code.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Traps, thrown as their exit code: 2 underflow, 3 overflow, 4 div by zero,
// 5 unknown opcode, 6 bad memory address, 7 call depth, 8 empty RET, 9 pc,
// 10 step limit, 11 output limit.
function run(p: Uint8Array, inp: Uint8Array): { o: Uint8Array; c: number } {
  const s = new Int32Array(256); // data stack
  const k = new Int32Array(64); // call stack
  const m = new Int32Array(256); // memory
  const b = new Uint8Array(65536); // output bytes
  const N = p.length;
  let sp = 0, cp = 0, pc = 0, ip = 0, ol = 0, st = 0;
  try {
    for (;;) {
      if (st === 1e6) throw 10; // step limit, before the next fetch
      if (pc < 0 || pc >= N) throw 9; // pc outside the program
      const op = p[pc];
      let im = 0;
      if (op === 1) im = 1;
      else if (op === 2) im = 4;
      else if (op >= 0x30 && op <= 0x33) im = 2;
      else if ((op > 7 && op < 16) || (op > 0x22 && op < 0x30) || (op > 0x34 && op < 0x40) || (op > 0x41 && op < 0x50) || op > 0x53) throw 5;
      if (pc + im >= N) throw 9; // immediate cut off by the end
      st++;
      const nx = pc + 1 + im;
      pc = nx;
      switch (op) {
        case 0x00: return { o: b.subarray(0, ol), c: 0 }; // HALT
        case 0x01: // PUSH8, sign-extended
          if (sp === 256) throw 3;
          s[sp++] = (p[pc - 1] << 24) >> 24;
          break;
        case 0x02: // PUSH32, little-endian
          if (sp === 256) throw 3;
          s[sp++] = p[pc - 4] | (p[pc - 3] << 8) | (p[pc - 2] << 16) | (p[pc - 1] << 24);
          break;
        case 0x03: // POP
          if (sp < 1) throw 2;
          sp--;
          break;
        case 0x04: // DUP
          if (sp < 1) throw 2;
          if (sp === 256) throw 3;
          s[sp] = s[sp - 1];
          sp++;
          break;
        case 0x05: // SWAP
          if (sp < 2) throw 2;
          { const t = s[sp - 1]; s[sp - 1] = s[sp - 2]; s[sp - 2] = t; }
          break;
        case 0x06: // OVER
          if (sp < 2) throw 2;
          if (sp === 256) throw 3;
          s[sp] = s[sp - 2];
          sp++;
          break;
        case 0x07: // ROT: ( a b c -- b c a )
          if (sp < 3) throw 2;
          { const a = s[sp - 3]; s[sp - 3] = s[sp - 2]; s[sp - 2] = s[sp - 1]; s[sp - 1] = a; }
          break;
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
        case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
        case 0x20: case 0x21: case 0x22: {
          if (sp < 2) throw 2;
          const y = s[sp - 1], x = s[sp - 2];
          let r: number;
          if (op === 0x10) r = (x + y) | 0;
          else if (op === 0x11) r = (x - y) | 0;
          else if (op === 0x12) r = Math.imul(x, y); // low 32 bits of the product
          else if (op === 0x13) {
            if (y === 0) throw 4;
            r = x === -2147483648 && y === -1 ? x : (x / y) | 0;
          } else if (op === 0x14) {
            if (y === 0) throw 4;
            r = y === -1 ? 0 : (x % y) | 0; // remainder takes the sign of x
          } else if (op === 0x15) {
            if (y === 0) throw 4;
            r = Math.floor((x >>> 0) / (y >>> 0)) | 0;
          } else if (op === 0x16) {
            if (y === 0) throw 4;
            r = ((x >>> 0) % (y >>> 0)) | 0;
          } else if (op === 0x18) r = x & y;
          else if (op === 0x19) r = x | y;
          else if (op === 0x1a) r = x ^ y;
          else if (op === 0x1c) r = x << (y & 31);
          else if (op === 0x1d) r = x >> (y & 31);
          else if (op === 0x1e) r = (x >>> (y & 31)) | 0;
          else if (op === 0x20) r = x === y ? 1 : 0;
          else if (op === 0x21) r = x < y ? 1 : 0;
          else r = (x >>> 0) < (y >>> 0) ? 1 : 0;
          sp -= 2;
          s[sp++] = r;
          break;
        }
        case 0x17: // NEG, wraps
          if (sp < 1) throw 2;
          s[sp - 1] = -s[sp - 1] | 0;
          break;
        case 0x1b: // NOT
          if (sp < 1) throw 2;
          s[sp - 1] = ~s[sp - 1];
          break;
        case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
          const rel = ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
          let take = true;
          if (op !== 0x30) {
            if (sp < 1) throw 2;
            const v = s[--sp];
            take = op === 0x31 ? v === 0 : v !== 0;
          }
          if (take) pc = nx + rel;
          break;
        }
        case 0x33: // CALL: push next, jump to the unsigned 16-bit target
          if (cp === 64) throw 7;
          k[cp++] = nx;
          pc = p[pc - 2] | (p[pc - 1] << 8);
          break;
        case 0x34: // RET
          if (cp === 0) throw 8;
          pc = k[--cp];
          break;
        case 0x40: // LOAD
          if (sp < 1) throw 2;
          { const a = s[sp - 1]; if (a < 0 || a >= 256) throw 6; s[sp - 1] = m[a]; }
          break;
        case 0x41: // STORE: ( v addr -- )
          if (sp < 2) throw 2;
          { const a = s[sp - 1], v = s[sp - 2]; if (a < 0 || a >= 256) throw 6; sp -= 2; m[a] = v; }
          break;
        case 0x50: { // PRINT: the value in decimal ASCII, no newline
          if (sp < 1) throw 2;
          const t = String(s[sp - 1]);
          if (ol + t.length > 65536) throw 11;
          for (let i = 0; i < t.length; i++) b[ol++] = t.charCodeAt(i);
          sp--;
          break;
        }
        case 0x51: // PUTC: one byte, the low 8 bits
          if (sp < 1) throw 2;
          if (ol + 1 > 65536) throw 11;
          b[ol++] = s[--sp] & 255;
          break;
        case 0x52: // IN: next input byte, or -1 once the input is used up
          if (sp === 256) throw 3;
          s[sp++] = ip < inp.length ? inp[ip++] : -1;
          break;
        case 0x53: // EXIT: exit with the low byte of the value
          if (sp < 1) throw 2;
          return { o: b.subarray(0, ol), c: s[--sp] & 255 };
        default: throw 5; // unreachable: unknown opcodes trap earlier
      }
    }
  } catch (e) {
    return { o: b.subarray(0, ol), c: e as number };
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const d = join(I, id);
  let prog: Buffer;
  try {
    prog = readFileSync(join(d, 'program.bin'));
  } catch {
    continue;
  }
  let inp = Buffer.alloc(0);
  try {
    inp = readFileSync(join(d, 'input.bin'));
  } catch {
    // No input file reads as empty input.
  }
  const { o, c } = run(prog, inp);
  const od = join(O, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), o);
  writeFileSync(join(od, 'exit.txt'), String(c) + '\n');
}
