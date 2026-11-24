// Tiny stack VM (ISA v1) for make.fun tiny-stack-vm-01: runs every bytecode
// program in MAKEFUN_INPUT_DIR, writes stdout.bin + exit.txt per id to
// MAKEFUN_OUTPUT_DIR. Node 22, stdlib only; no network, no clock.
// 32-bit wrapping ints, 256-value stack, 64-deep call stack, 256 memory
// words, 65,536 output cap, 1,000,000 step cap; ten traps end a program
// at once with their own exit code, keeping output.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const STACK_MAX = 256, CALLS_MAX = 64, MEM_WORDS = 256, STEP_LIMIT = 1_000_000, OUT_MAX = 65_536;
// [byte, imm, pops, pushes] per opcode; drives the step checks.
const SPEC: [number, number, number, number][] = [
  [0x00,0,0,0],[0x01,1,0,1],[0x02,4,0,1],[0x03,0,1,0],[0x04,0,1,2],[0x05,0,2,2],[0x06,0,2,3],[0x07,0,3,3],
  [0x10,0,2,1],[0x11,0,2,1],[0x12,0,2,1],[0x13,0,2,1],[0x14,0,2,1],[0x15,0,2,1],[0x16,0,2,1],[0x17,0,1,1],
  [0x18,0,2,1],[0x19,0,2,1],[0x1a,0,2,1],[0x1b,0,1,1],[0x1c,0,2,1],[0x1d,0,2,1],[0x1e,0,2,1],
  [0x20,0,2,1],[0x21,0,2,1],[0x22,0,2,1],
  [0x30,2,0,0],[0x31,2,1,0],[0x32,2,1,0],[0x33,2,0,0],[0x34,0,0,0],
  [0x40,0,1,1],[0x41,0,2,0],[0x50,0,1,0],[0x51,0,1,0],[0x52,0,0,1],[0x53,0,1,0],
];
const IMM = new Int8Array(256).fill(-1);
const POPS = new Int8Array(256);
const PUSHES = new Int8Array(256);
for (const [byte, imm, pops, pushes] of SPEC) { IMM[byte] = imm; POPS[byte] = pops; PUSHES[byte] = pushes; }
const enc = new TextEncoder();
function runVM(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; exit: number } {
  const n = prog.length;
  const stack = new Int32Array(STACK_MAX);
  const calls = new Int32Array(CALLS_MAX);
  const mem = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUT_MAX);
  let sp = 0, cp = 0, olen = 0, ipos = 0, pc = 0, steps = 0;
  const finish = (exit: number): { out: Uint8Array; exit: number } => ({ out: out.slice(0, olen), exit });
  for (;;) {
    if (steps === STEP_LIMIT) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return finish(5);
    if (pc + imm >= n) return finish(9);
    steps++;
    const at = pc, next = pc + 1 + imm;
    if (sp < POPS[op]) return finish(2);
    if (sp - POPS[op] + PUSHES[op] > STACK_MAX) return finish(3);
    pc = next;
    switch (op) {
      case 0x00: return finish(0);
      case 0x01: stack[sp++] = (prog[at + 1] << 24) >> 24; break;
      case 0x02: stack[sp++] = prog[at + 1] | (prog[at + 2] << 8) | (prog[at + 3] << 16) | (prog[at + 4] << 24); break;
      case 0x03: sp--; break;
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break;
      case 0x05: { const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; break; }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break;
      case 0x07: { const a = stack[sp - 3]; stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a; break; }
      case 0x17: stack[sp - 1] = (-stack[sp - 1]) | 0; break;
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1], a = stack[sp - 2];
        let r = 0;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: if (b === 0) return finish(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: if (b === 0) return finish(4); r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2; stack[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[at + 1] | (prog[at + 2] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = stack[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === CALLS_MAX) return finish(7);
        calls[cp++] = next; pc = prog[at + 1] | (prog[at + 2] << 8);
        break;
      case 0x34:
        if (cp === 0) return finish(8);
        pc = calls[--cp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return finish(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1], v = stack[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return finish(6);
        sp -= 2; mem[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(stack[sp - 1]));
        if (olen + bytes.length > OUT_MAX) return finish(11);
        sp--; out.set(bytes, olen); olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OUT_MAX) return finish(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52: stack[sp++] = ipos < input.length ? input[ipos++] : -1; break;
      case 0x53: return finish(stack[--sp] & 255);
    }
  }
}
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const entry of readdirSync(IN_DIR, { withFileTypes: true }).sort((x, y) => (x.name < y.name ? -1 : 1))) {
  if (!entry.isDirectory()) continue;
  const id = entry.name;
  const prog = readFileSync(join(IN_DIR, id, 'program.bin'));
  const input = readFileSync(join(IN_DIR, id, 'input.bin'));
  const { out, exit } = runVM(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), out);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), String(exit) + '\n');
}
