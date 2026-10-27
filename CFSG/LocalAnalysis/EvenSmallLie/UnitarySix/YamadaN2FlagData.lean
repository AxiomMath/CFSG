module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Data

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def inV1 (r : ℕ) : Bool := r == 0 || r == 9

@[expose] def inW0 (r : ℕ) : Bool := r ≤ 4 || (9 ≤ r && r ≤ 13)

@[expose] def w0pC (i : ℕ) : ℕ := if i < 4 then i + 1 else i + 6

@[expose] def w1C (j : ℕ) : ℕ := if j < 4 then j + 5 else j + 10

@[expose] def c2C (k : ℕ) : ℕ := if k < 8 then w0pC k else w1C (k - 8)

@[expose] def w0pI (r : ℕ) : ℕ :=
  if 1 ≤ r ∧ r ≤ 4 then r - 1 else if 10 ≤ r ∧ r ≤ 13 then r - 6 else 8

@[expose] def w1I (r : ℕ) : ℕ :=
  if 5 ≤ r ∧ r ≤ 8 then r - 5 else if 14 ≤ r ∧ r < 18 then r - 10 else 8

@[expose] def id18 : Array ℕ := Array.ofFn (n := 18) fun r => 2 ^ (r : ℕ)

@[expose] def tauBits : Array ℕ :=
  #[513, 1026, 2052, 4104, 8208, 16416, 32832, 65664, 131328, 512, 1024, 2048, 4096, 8192, 16384,
    32768, 65536, 131072]

@[expose] def eBits18 (m : ℕ) : Array ℕ :=
  bd9Bits (genABits (Fin.ofNat 12 m)) (genABits (Fin.ofNat 12 m))

@[expose] def nuS (j : ℕ) : Fin 12 :=
  if j = 0 then 6 else if j = 1 then 7 else if j = 2 then 10 else 11

@[expose] def vBits (j : ℕ) : Array ℕ := bd9Bits (genABits (nuS j)) (genABits (nuS j))

@[expose] def eProdBits (mask : ℕ) : Array ℕ :=
  (List.range 4).foldl (fun acc n => if mask.testBit n then bmul 18 18 acc (eBits18 n) else acc)
    id18

@[expose] def blk1Bits (M : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun i => bitsOf 8 fun j => (M.getD (w0pC i) 0).testBit (w1C j)

@[expose] def emb1Bits (B : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 18) fun r => bitsOf 18 fun c =>
    w0pI r < 8 && w1I c < 8 && (B.getD (w0pI r) 0).testBit (w1I c)

@[expose] def blk2Bits (M : Array ℕ) : ℕ :=
  bitsOf 32 fun k => (M.getD (if k < 16 then 0 else 9) 0).testBit (c2C (k % 16))

@[expose] def c2I (c : ℕ) : ℕ :=
  if 1 ≤ c ∧ c ≤ 4 then c - 1 else if 10 ≤ c ∧ c ≤ 13 then c - 6
  else if 5 ≤ c ∧ c ≤ 8 then c + 3 else if 14 ≤ c ∧ c < 18 then c - 2 else 16

@[expose] def emb2Bits (d : ℕ) : Array ℕ :=
  Array.ofFn (n := 18) fun r =>
    if (r : ℕ) = 0 then bitsOf 18 fun c => c2I c < 16 && d.testBit (c2I c)
    else if (r : ℕ) = 9 then bitsOf 18 fun c => c2I c < 16 && d.testBit (16 + c2I c)
    else 0

@[expose] def t2Bits : Array ℕ := #[17, 34, 68, 136, 16, 32, 64, 128]

@[expose] def aBits2 : ℕ → Array ℕ
  | 0 => #[1, 0, 4, 8, 16, 0, 64, 128]
  | 1 => #[0, 1, 8, 12, 0, 16, 128, 192]
  | 2 => #[12, 8, 2, 0, 192, 128, 32, 0]
  | _ => #[8, 4, 0, 2, 128, 64, 0, 32]

@[expose] def n0Bits2 : ℕ → Array ℕ
  | 0 => #[5, 10, 4, 8, 80, 160, 64, 128]
  | 1 => #[13, 6, 4, 8, 208, 96, 64, 128]
  | 2 => #[1, 2, 5, 10, 16, 32, 80, 160]
  | _ => #[1, 2, 7, 9, 16, 32, 112, 144]

@[expose] def n1Bits2 : ℕ → Array ℕ
  | 0 => #[11, 2, 6, 8, 176, 32, 96, 128]
  | 1 => #[7, 2, 4, 10, 112, 32, 64, 160]
  | 2 => #[1, 11, 5, 8, 16, 176, 80, 128]
  | _ => #[1, 15, 5, 9, 16, 240, 80, 144]

@[expose] def cMask2 : ℕ → ℕ → ℕ
  | 0, 0 => 5
  | 0, 1 => 10
  | 0, 2 => 4
  | 0, _ => 8
  | 1, 0 => 9
  | 1, 1 => 14
  | 1, 2 => 4
  | 1, _ => 8
  | 2, 0 => 1
  | 2, 1 => 2
  | 2, 2 => 5
  | 2, _ => 10
  | _, 0 => 1
  | _, 1 => 2
  | _, 2 => 6
  | _, _ => 11

@[expose] def msum2 (k mask : ℕ) (f : ℕ → Array ℕ) : Array ℕ :=
  (List.range k).foldl (fun acc m => if mask.testBit m then bxor 8 acc (f m) else acc) zero8

@[expose] def lamMaskOf (L : Array ℕ) (j m : ℕ) : ℕ :=
  (L.getD (2 * j + m / 2) 0 >>> (4 * (m % 2))) % 16

@[expose] def dBlock2 (B : ℕ → Array ℕ) (k : ℕ) : Array ℕ :=
  if k < 4 then bxor 8 (bmul 8 8 (bmul 8 8 t2Bits (B k)) t2Bits) (B k)
  else
    let j := (k - 4) / 4
    let m := (k - 4) % 4
    bxor 8 (bxor 8 (bmul 8 8 (bmul 8 8 (n0Bits2 j) (B m)) (n1Bits2 j)) (msum2 4 (cMask2 j m) B))
      (msum2 4 (lamMaskOf (B 4) j m) aBits2)

@[expose] def dFb2 (v : ℕ) : ℕ := packBlks 20 (dBlock2 fun s => unpackBlk v s)

@[expose] def ofBlocks2 (b : List (Array ℕ)) : ℕ := packBlks 5 fun s => b.getD s zero8

@[expose] def dY0Blocks2 : List (Array ℕ) :=
  [#[0, 0, 0, 0, 17, 0, 68, 136], #[0, 0, 0, 0, 0, 17, 136, 204], #[0, 0, 0, 0, 204, 136, 34, 0],
    #[0, 0, 0, 0, 136, 68, 0, 34], zero8]

@[expose] def dDirBlocks2 : ℕ → List (Array ℕ)
  | 0 =>
    [#[16, 0, 64, 128, 0, 0, 0, 0], #[0, 16, 128, 192, 0, 0, 0, 0], #[192, 128, 32, 0, 0, 0, 0, 0],
      #[128, 64, 0, 32, 0, 0, 0, 0], zero8]
  | _ =>
    [#[0, 16, 128, 192, 0, 0, 0, 0], #[16, 16, 192, 64, 0, 0, 0, 0], #[128, 64, 0, 32, 0, 0, 0, 0],
      #[64, 192, 32, 32, 0, 0, 0, 0], zero8]

@[expose] def dY0b : ℕ := ofBlocks2 dY0Blocks2

@[expose] def dDir2 (q : ℕ) : ℕ := ofBlocks2 (dDirBlocks2 q)

@[expose] def ambLam (i m' : ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun r =>
    let j := (r : ℕ) / 2
    (List.range 2).foldl (fun acc h =>
      let m := 2 * ((r : ℕ) % 2) + h
      acc ||| (((if m = i then cMask2 j m' else 0) ^^^
        (if (cMask2 j m).testBit i then 2 ^ m' else 0)) <<< (4 * h))) 0

@[expose] def dAmb2 (i m' : ℕ) : ℕ :=
  packBlks 5 fun s => if s < 4 then (if s = i then aBits2 m' else zero8) else ambLam i m'

@[expose] def dCols2 : Array ℕ :=
  Array.ofFn (n := 18) fun c =>
    if (c : ℕ) < 2 then dDir2 c else dAmb2 (((c : ℕ) - 2) / 4) (((c : ℕ) - 2) % 4)

@[expose] def dTarget2 : ℕ := packBlks 20 fun k => if k < 4 then aBits2 k else zero8

@[expose] def candBlock (z s : ℕ) : Array ℕ :=
  bxor 8 (bxor 8 (dY0Blocks2.getD s zero8)
    (if z.testBit 0 then (dDirBlocks2 0).getD s zero8 else zero8))
    (if z.testBit 1 then (dDirBlocks2 1).getD s zero8 else zero8)

@[expose] def y0Check2 : Bool := dFb2 dY0b == dTarget2

@[expose] def tnCheck : Bool :=
  ((List.range 4).all fun j =>
    bmul 8 8 t2Bits (n0Bits2 j) == bmul 8 8 (n0Bits2 j) t2Bits &&
      bmul 8 8 t2Bits (n1Bits2 j) == bmul 8 8 (n1Bits2 j) t2Bits) &&
  (List.range 4).all fun j => (List.range 4).all fun m =>
    bmul 18 18 (bmul 18 18 (vBits j) (eBits18 m)) (vBits j) == eProdBits (cMask2 j m)

@[expose] def aIndepCheck : Bool :=
  (List.range 16).all fun μ => μ == 0 ||
    (List.range 8).any fun r => (List.range 8).any fun c => ((msum2 4 μ aBits2).getD r 0).testBit c

@[expose] def aConjCheck2 : Bool :=
  (List.range 4).all (fun j => (List.range 4).all fun m =>
    bmul 8 8 (bmul 8 8 (n0Bits2 j) (aBits2 m)) (n1Bits2 j) == msum2 4 (cMask2 j m) aBits2) &&
  (List.range 4).all fun m =>
    bxor 8 (bmul 8 8 (bmul 8 8 t2Bits (aBits2 m)) t2Bits) (aBits2 m) == zero8

@[expose] def yBits (z m : ℕ) : Array ℕ := bxor 18 id18 (emb1Bits (candBlock z m))

@[expose] def tytBits (z m : ℕ) : Array ℕ := bmul 18 18 (bmul 18 18 tauBits (yBits z m)) tauBits

@[expose] def emb2m (v m : ℕ) : Array ℕ := emb2Bits ((v >>> (32 * m)) % 2 ^ 32)

@[expose] def bitList (mask : ℕ) : List ℕ := (List.range 4).filter fun n => mask.testBit n

@[expose] def yProd (z : ℕ) (l : List ℕ) : Array ℕ :=
  l.foldl (fun acc n => bmul 18 18 acc (yBits z n)) id18

@[expose] def lamZ (z j m : ℕ) : ℕ := lamMaskOf (candBlock z 4) j m

@[expose] def linE (z j m v : ℕ) : Array ℕ :=
  let l := bitList (cMask2 j m)
  let El := eProdBits (lamZ z j m)
  (List.range l.length).foldl (fun acc i =>
      bxor 18 acc (bmul 18 18 (emb2m v (l.getD i 0)) (bmul 18 18 (yProd z (l.drop (i + 1))) El)))
    (bmul 18 18 (bmul 18 18 (vBits j) (emb2m v m)) (vBits j))

@[expose] def s2Block (z v k : ℕ) : ℕ :=
  if k < 4 then
    blk2Bits (bxor 18 (bmul 18 18 (emb2m v k) (tytBits z k))
      (bmul 18 18 (bmul 18 18 tauBits (emb2m v k)) tauBits))
  else blk2Bits (linE z ((k - 4) / 4) ((k - 4) % 4) v)

@[expose] def s2TBlock (z k : ℕ) : ℕ :=
  if k < 4 then blk2Bits (bxor 18 (eBits18 k) (bmul 18 18 (yBits z k) (tytBits z k)))
  else
    let j := (k - 4) / 4
    let m := (k - 4) % 4
    blk2Bits (bxor 18 (bmul 18 18 (yProd z (bitList (cMask2 j m))) (eProdBits (lamZ z j m)))
      (bmul 18 18 (bmul 18 18 (vBits j) (yBits z m)) (vBits j)))

@[expose] def catW (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a % 2 ^ w ||| catW w l <<< w

@[expose] def cat20 (f : ℕ → ℕ) : ℕ := catW 32 ((List.range 20).map f)

@[expose] def s2Fb (z v : ℕ) : ℕ := cat20 (s2Block z v)

@[expose] def s2Target (z : ℕ) : ℕ := cat20 (s2TBlock z)

@[expose] def s2Sol (z : ℕ) : ℕ :=
  if z = 0 then 45546828053754412204092599877857574912 else 3012226851262671947090508201351844128

@[expose] def s2Farkas (z : ℕ) : ℕ :=
  if z = 2 then 3213876088517980551519485614341126438277525485078249266479378
  else 3213876088517980551519485614341126438277525485078249266479379

@[expose] def candXBits (z m : ℕ) : Array ℕ := bxor 18 (yBits z m) (emb2m (s2Sol z) m)

@[expose] def par640 (n : ℕ) : Bool := xorFold 640 fun i => n.testBit i

@[expose] def clsN (r : ℕ) : ℕ := if inV1 r then 0 else if inW0 r then 1 else 2

@[expose] def fixV1B (A : Array ℕ) : Bool :=
  (List.range 18).all fun r => (List.range 18).all fun k =>
    clsN k != 0 || (A.getD r 0).testBit k == (r == k)

@[expose] def presV1B (A : Array ℕ) : Bool :=
  (List.range 18).all fun r => (List.range 18).all fun k =>
    clsN k != 0 || clsN r == 0 || !(A.getD r 0).testBit k

@[expose] def triB (A : Array ℕ) : Bool :=
  (List.range 18).all fun r => (List.range 18).all fun c =>
    !(clsN c < clsN r) || !(A.getD r 0).testBit c

@[expose] def bdiagB (A : Array ℕ) : Bool :=
  (List.range 18).all fun r => (List.range 18).all fun c =>
    clsN c == clsN r || !(A.getD r 0).testBit c

@[expose] def flagB (A : Array ℕ) : Bool :=
  (List.range 18).all fun r => (List.range 18).all fun c =>
    (clsN r ≤ 1 && clsN c == 2) || (clsN r == 0 && clsN c == 1) ||
      (A.getD r 0).testBit c == (r == c)

@[expose] def lay1B (A : Array ℕ) : Bool :=
  (List.range 18).all fun r => (List.range 18).all fun c =>
    (clsN r == 1 && clsN c == 2) || (A.getD r 0).testBit c == (r == c)

@[expose] def subBits (rr cc : ℕ → ℕ) (A : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun i => bitsOf 8 fun j => (A.getD (rr i) 0).testBit (cc j)

@[expose] def shapeCheck : Bool :=
  presV1B tauBits && bdiagB tauBits && bmul 18 18 tauBits tauBits == id18 &&
  subBits w0pC w0pC tauBits == t2Bits && subBits w1C w1C tauBits == t2Bits &&
  ((List.range 4).all fun m => fixV1B (eBits18 m) && flagB (eBits18 m) &&
    blk1Bits (eBits18 m) == aBits2 m) &&
  ((List.range 4).all fun j => fixV1B (vBits j) && triB (vBits j) &&
    bmul 18 18 (vBits j) (vBits j) == id18 && subBits w0pC w0pC (vBits j) == n0Bits2 j &&
    subBits w1C w1C (vBits j) == n1Bits2 j) &&
  ((List.range 4).all fun z => (List.range 4).all fun m =>
    lay1B (yBits z m) && blk1Bits (yBits z m) == candBlock z m)

@[expose] def w0Wit (i : ℕ) : ℕ × ℕ :=
  match i with
  | 0 => (0, 4) | 1 => (0, 36) | 2 => (1, 34) | 3 => (0, 128) | 4 => (0, 256)
  | 9 => (0, 2048) | 10 => (0, 18432) | 11 => (1, 17408) | 12 => (0, 65536) | _ => (0, 131072)

@[expose] def w0List : List ℕ := [0, 1, 2, 3, 4, 9, 10, 11, 12, 13]

@[expose] def witCheck : Bool :=
  w0List.all (fun i =>
    let p := w0Wit i
    p.1 < 4 && (bmulVec 18 18 (eBits18 p.1) p.2 ^^^ p.2) == 2 ^ i) &&
  [0, 9].all fun i => (List.range 18).all fun c => !(w0Wit i).2.testBit c || inW0 c

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
