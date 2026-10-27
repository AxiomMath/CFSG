module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1CohData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open CFSG.Monster.B.Co2.Native

@[expose] def leviWord : List ℕ := [1, 2, 3, 0, 2, 0, 1]

@[expose] def leviRows : Array ℕ := #[57, 30, 52, 24, 16, 32]

@[expose] def leviArr (ε : Eps) (w : List ℕ) : Array ℕ :=
  w.foldr (fun s acc => compA (deg ε) (pArr ε s) acc) (idA (deg ε))

@[expose] def leviCheck : Bool :=
  let n := deg .minus
  let k := leviArr .minus leviWord
  wordRows .minus leviWord == leviRows && eqA n (compA n (compA n k k) (compA n k k)) (idA n)

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
