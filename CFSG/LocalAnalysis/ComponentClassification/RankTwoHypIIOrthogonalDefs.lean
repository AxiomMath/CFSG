module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ComponentClassification.RankTwoHypIIOrthogonal

open Subgroup CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

@[expose] def OrthLinearConfigFree : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), 4 ≤ n →
    ∀ Q : QuadraticForm K (Fin (2 * n) → K), Q.polarBilin.Nondegenerate →
    (∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) →
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q →
    ∀ F : Subgroup (GL (Fin (2 * n)) K), F ≤ matrixIsometries Q → IsElemAbelian 2 F →
      4 ≤ Nat.card F → ¬ F ≤ matrixDerived Q →
      (∀ s ∈ F, s ≠ 1 →
        2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank) →
      (∀ x ∈ F, x ≠ 1 →
        matrixDerived Q ⊓ centralizer ({x} : Set (GL (Fin (2 * n)) K)) ≤
          normalizer (F : Set (GL (Fin (2 * n)) K))) →
      False

end CFSG.ComponentClassification.RankTwoHypIIOrthogonal
