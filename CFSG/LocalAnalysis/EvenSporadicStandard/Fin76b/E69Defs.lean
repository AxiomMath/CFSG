module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableDefs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.E69

open AutETable

@[expose] def isAutArr (m : ℕ → ℕ → ℕ) (A : Array ℕ) : Bool :=
  (List.range 32).all fun a => decide (ix A a < 32) && (List.range 32).all fun b =>
    ix A (m a b) == m (ix A a) (ix A b) && (ix A a != ix A b || a == b)

end CFSG.EvenSporadicStandard.Fin76b.E69
