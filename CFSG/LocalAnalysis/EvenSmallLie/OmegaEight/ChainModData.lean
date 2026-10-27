module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1CohData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open CFSG.EvenSmallLie.UnitarySix.YamadaPar Stage1

@[expose] def colBits (M : Array ℕ) (l : ℕ) : ℕ := bitsOf 6 fun j => (M.getD j 0).testBit l

@[expose] def modBlock (ε : Eps) (C : ℕ → Array ℕ) (k : ℕ) : Array ℕ :=
  bxor 6 (bxor 6 (bmul 6 6 (combo6 (colBits (genRows ε (k / 6)) (k % 6)) C 6) (genRows ε (k / 6)))
      (bmul 6 6 (genRows ε (k / 6)) (C (k % 6))))
    (if ((C 6).getD (k / 6) 0).testBit (k % 6) then genRows ε (k / 6) else zero6)

@[expose] def modFb (ε : Eps) (v : ℕ) : ℕ := packN 6 36 (modBlock ε (unpackN 6 v))

@[expose] def modSol (ε : Eps) (m : ℕ) : ℕ :=
  packN 6 7 fun s =>
    if s < 6 then (if s = m then id6 else zero6)
    else Array.ofFn (n := 6) fun i => (genRows ε i).getD m 0 ^^^ 2 ^ m

end CFSG.EvenSmallLie.OmegaEight.Chain
