module

public import CFSG.ClassicalInvolution.ModelFacts.MF15Defs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem linearIndependent_pair_of_not_eigen {u w : V} (hu : u ≠ 0) (hw : ¬ ∃ c : F, w = c • u) :
    LinearIndependent F ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    simp only [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hu, rfl⟩
  · exfalso
    apply hw
    refine ⟨-(b⁻¹ * a), ?_⟩
    have : b • w = -(a • u) := eq_neg_of_add_eq_zero_right hab
    calc w = b⁻¹ • (b • w) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • (-(a • u)) := by rw [this]
      _ = -(b⁻¹ * a) • u := by rw [smul_neg, smul_smul, neg_smul]

end CFSG.ClassicalInvolution.ModelFacts.MF15
