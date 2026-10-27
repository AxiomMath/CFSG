module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Stage1

@[expose] def colsActAux (C : List ℕ) (z : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => colsActAux C z n ^^^ (if z.testBit n then C.getD n 0 else 0)

@[expose] def colsAct (C : List ℕ) (z : ℕ) : ℕ := colsActAux C z 6

@[expose] def fixCount (C : List ℕ) : ℕ :=
  ((List.range 64).filter fun z => colsAct C z == z).length

@[expose] def isInvol (C : List ℕ) : Bool :=
  ((List.range 6).all fun j => colsAct C (C.getD j 0) == 2 ^ j) &&
    C != (List.range 6).map (2 ^ ·)

@[expose] def invCheck (ε : Eps) : Bool :=
  (oCols ε).all fun C => dickC C || !isInvol C || fixCount C == 16

end CFSG.EvenSmallLie.OmegaEight.Chain
