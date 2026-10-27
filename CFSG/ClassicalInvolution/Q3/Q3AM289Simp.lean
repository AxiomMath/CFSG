module

public import CFSG.ClassicalInvolution.Q3.Q3AM289Shape

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3

section Simple


theorem isQuasisimple_of_rows {c : CompData}
    (hc : c = CompData.model .PSU 3 ∨ c = CompData.model .G2 0 ∨
      c = CompData.model .trialityD4 0) : CFSG.Open.IsQuasisimple c.G := by
  rcases hc with rfl | rfl | rfl
  · exact (ModelFacts.modelClauseZero .PSU 3 3 1 Nat.prime_three trivial
      Q3PP.statedLieAdmissible_psu3).1
  · exact (ModelFacts.modelClauseZero .G2 0 3 1 Nat.prime_three trivial
      (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 3 1 from
        ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩)).1
  · exact (ModelFacts.modelClauseZero .trialityD4 0 3 1 Nat.prime_three trivial
      (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1 from
        ⟨Nat.prime_three, le_rfl, rfl⟩)).1

theorem isSimpleGroup_of_rows {c : CompData}
    (hc : c = CompData.model .PSU 3 ∨ c = CompData.model .G2 0 ∨
      c = CompData.model .trialityD4 0) : IsSimpleGroup c.G :=
  Q3Y.isSimpleGroup_of_center_eq_bot (isQuasisimple_of_rows hc) (center_eq_bot_of_rows hc)

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}

theorem S3Shape.isSimpleGroup (h : S3Shape Φ) : IsSimpleGroup Y := by
  obtain ⟨c, ψ, hc, hbij, -⟩ := h.exists_bijective
  have : IsSimpleGroup c.G := isSimpleGroup_of_rows hc
  exact MulEquiv.isSimpleGroup (MulEquiv.ofBijective ψ hbij).symm

theorem S3Shape.exists_noncomm (h : S3Shape Φ) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨c, ψ, hc, hbij, -⟩ := h.exists_bijective
  obtain ⟨a, b, hab⟩ := Q3Y.exists_noncomm_of_isQuasisimple (isQuasisimple_of_rows hc)
  exact ⟨ψ a, ψ b, fun h' => hab (hbij.1 (by rw [map_mul, map_mul]; exact h'))⟩

end Simple

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
