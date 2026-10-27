module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Data

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def tBits : Array ℕ := #[17, 34, 68, 136, 16, 32, 64, 128]

@[expose] def aBits : ℕ → Array ℕ
  | 0 => #[1, 2, 0, 0, 16, 32, 0, 0]
  | 1 => #[0, 0, 4, 8, 0, 0, 64, 128]
  | 2 => #[4, 8, 1, 2, 64, 128, 16, 32]
  | _ => #[8, 12, 3, 1, 128, 192, 48, 16]

@[expose] def n0Bits : ℕ → Array ℕ
  | 0 => #[4, 8, 1, 2, 64, 128, 16, 32]
  | _ => #[8, 12, 11, 13, 128, 192, 176, 208]

@[expose] def n1Bits : ℕ → Array ℕ
  | 0 => #[4, 8, 1, 2, 64, 128, 16, 32]
  | _ => #[8, 12, 15, 5, 128, 192, 240, 80]

@[expose] def cMask : ℕ → ℕ → ℕ
  | 0, 0 => 2
  | 0, 1 => 1
  | 0, 2 => 4
  | 0, _ => 12
  | _, 0 => 2
  | _, 1 => 7
  | _, 2 => 14
  | _, _ => 10

@[expose] def msum (k mask : ℕ) (f : ℕ → Array ℕ) : Array ℕ :=
  (List.range k).foldl (fun acc m => if mask.testBit m then bxor 8 acc (f m) else acc) zero8

@[expose] def hiMask : Array ℕ := #[0, 0, 0, 0, 16, 32, 64, 128]

@[expose] def dBlock (B : ℕ → Array ℕ) (k : ℕ) : Array ℕ :=
  if k < 4 then bxor 8 (bmul 8 8 (bmul 8 8 tBits (B k)) tBits) (B k)
  else if k < 12 then
    let j := (k - 4) / 4
    let i := (k - 4) % 4
    bxor 8 (bxor 8 (bmul 8 8 (bmul 8 8 (n0Bits j) (B i)) (n1Bits j)) (msum 4 (cMask j i) B))
      (msum 4 ((B 4).getD (4 * j + i) 0) aBits)
  else bmul 8 8 (B 4) hiMask

@[expose] def dFb (v : ℕ) : ℕ := packBlks 13 (dBlock fun s => unpackBlk v s)

@[expose] def ofBlocks (b : List (Array ℕ)) : ℕ := packBlks 5 fun s => b.getD s zero8

@[expose] def dY0Blocks : List (Array ℕ) :=
  [#[0, 0, 0, 0, 17, 34, 0, 0], #[0, 0, 0, 0, 0, 0, 68, 136], #[0, 0, 0, 0, 68, 136, 17, 34],
    #[0, 0, 0, 0, 136, 204, 51, 17], #[0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def dY0 : ℕ := ofBlocks dY0Blocks

@[expose] def dDirBlocks : ℕ → List (Array ℕ)
  | 0 =>
    [#[2, 3, 0, 0, 32, 48, 0, 0], #[0, 0, 8, 12, 0, 0, 128, 192], #[0, 0, 1, 2, 0, 0, 16, 32],
      #[0, 0, 3, 1, 0, 0, 48, 16], #[0, 0, 4, 12, 0, 8, 14, 8]]
  | 1 =>
    [#[16, 32, 0, 0, 0, 0, 0, 0], #[0, 0, 64, 128, 0, 0, 0, 0], #[64, 128, 16, 32, 0, 0, 0, 0],
      #[128, 192, 48, 16, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0]]
  | _ =>
    [#[32, 48, 0, 0, 0, 0, 0, 0], #[0, 0, 128, 192, 0, 0, 0, 0], #[128, 192, 32, 48, 0, 0, 0, 0],
      #[192, 64, 16, 32, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def dDir (q : ℕ) : ℕ := ofBlocks (dDirBlocks q)

@[expose] def ambRow (i m j i' : ℕ) : ℕ :=
  bitsOf 4 fun m' =>
    ((i' == i) && (cMask j m).testBit m') ^^ ((m' == m) && (cMask j i').testBit i)

@[expose] def dAmb (i m : ℕ) : ℕ :=
  packBlks 5 fun s =>
    if s < 4 then (if s = i then aBits m else zero8)
    else Array.ofFn (n := 8) fun r => ambRow i m ((r : ℕ) / 4) ((r : ℕ) % 4)

@[expose] def dCols : Array ℕ :=
  Array.ofFn (n := 19) fun c =>
    if (c : ℕ) < 3 then dDir c else dAmb (((c : ℕ) - 3) / 4) (((c : ℕ) - 3) % 4)

@[expose] def dTarget : ℕ := packBlks 13 fun k => if k < 4 then aBits k else zero8

@[expose] def aConjCheck : Bool :=
  (List.range 2).all (fun j => (List.range 4).all fun i =>
    bmul 8 8 (bmul 8 8 (n0Bits j) (aBits i)) (n1Bits j) == msum 4 (cMask j i) aBits) &&
  (List.range 4).all fun m =>
    bxor 8 (bmul 8 8 (bmul 8 8 tBits (aBits m)) tBits) (aBits m) == zero8

@[expose] def y0Check : Bool := dFb dY0 == dTarget

@[expose] def dCheck : Bool := certCheck (5 * 64) 19 (13 * 64) (linBits (5 * 64) (13 * 64) dFb) dCols

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
