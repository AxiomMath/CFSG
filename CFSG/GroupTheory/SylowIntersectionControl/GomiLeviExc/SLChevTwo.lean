module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLChev
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isChevTwo_psl {n : ℕ} (K : Type) [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n ∨ (n = 2 ∧ 4 ≤ Nat.card K)) :
    IsChevTwo (Matrix.SpecialLinearGroup (Fin n) K ⧸
      center (Matrix.SpecialLinearGroup (Fin n) K)) :=
  isChevTwo_of_classicalTwoOrG2
    (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_sl (F := K) hn).2

end CFSG.GroupTheory.GomiLeviExc
