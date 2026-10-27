module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParDData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def id16 : Array ℕ := Array.ofFn (n := 16) fun r => 2 ^ (r : ℕ)

@[expose] def rho16 (A : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun r =>
    if (r : ℕ) < 8 then A.getD r 0 % 256 else (A.getD (r - 8) 0 % 256) <<< 8

@[expose] def inW0 (r : ℕ) : Bool := r < 4 || (8 ≤ r && r < 12)

@[expose] def posW0 (r : ℕ) : ℕ := if r < 4 then r else r - 4

@[expose] def inW1 (c : ℕ) : Bool := (4 ≤ c && c < 8) || (12 ≤ c && c < 16)

@[expose] def posW1 (c : ℕ) : ℕ := if c < 8 then c - 4 else c - 8

@[expose] def embed16 (ψ : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun r => bitsOf 16 fun c =>
    inW0 r && inW1 c && (ψ.getD (posW0 r) 0).testBit (posW1 c)

@[expose] def candBits (z i : ℕ) : Array ℕ :=
  bxor 8 (dY0Blocks.getD i zero8) (msum 3 z fun q => (dDirBlocks q).getD i zero8)

@[expose] def dGen (z k : ℕ) : Array ℕ :=
  bxor 16 id16 (embed16 (if k < 4 then aBits k else candBits z (k - 4)))

@[expose] def formGen (z k : ℕ) : Array ℕ :=
  if k = 0 then rho16 (genBits 0) else if k = 1 then rho16 (genBits 1) else dGen z (k - 2)

@[expose] def diag16 (B : Array ℕ) : Array ℕ := Array.ofFn (n := 16) fun r => B.getD r 0 &&& 2 ^ (r : ℕ)

@[expose] def formBlock (z : ℕ) (B : Array ℕ) (k : ℕ) : Array ℕ :=
  if k = 0 then bxor 16 B (btr 16 16 B)
  else if k = 1 then diag16 B
  else bxor 16 (bmul 16 16 (bmul 16 16 (btr 16 16 (formGen z (k - 2))) B) (formGen z (k - 2))) B

@[expose] def formFb (z v : ℕ) : ℕ := packN 16 12 (formBlock z (unpackN 16 v 0))

@[expose] def formCheck (z : ℕ) : Bool := injCheck 256 (12 * 256) (linBits 256 (12 * 256) (formFb z))

@[expose] def formsCheck : Bool := formCheck 4 && formCheck 5 && formCheck 6 && formCheck 7

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
