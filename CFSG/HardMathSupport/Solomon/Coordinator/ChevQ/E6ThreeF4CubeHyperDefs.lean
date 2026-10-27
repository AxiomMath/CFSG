module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open CFSG.Open TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Statements


@[expose] def F4NonToralNegHyperplane : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
    SeitzExcOpenRest4.ThreeScope LieTypeIndex.F4 K →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → IsEmpty (LangPlaneData .F4 K E₀) →
      ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ D : LangPlaneData .F4 K F,
        ∀ u : Fin Tag.F4.rank → ℤ, D.w • u = -u

@[expose] def F4NonToralSplitHyperplane : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
    SeitzExcOpenRest4.ThreeScope LieTypeIndex.F4 K →
    ∀ E₀ : Subgroup (adjointGroup .F4 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → IsEmpty (LangPlaneData .F4 K E₀) →
      ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ D : LangPlaneData .F4 K F, D.w = 1

end Statements

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
