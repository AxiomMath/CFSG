module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PSL9

open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] [Finite F]

theorem eq_zneg_of_mem_center (hF : Nat.card F = 3) {g : SL(4, F)}
    (hg : g ∈ Subgroup.center SL(4, F)) (hne : g ≠ 1) : g = zneg F := by
  obtain ⟨r, hr4, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have : Fintype F := Fintype.ofFinite F
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr4
  have hr2 : r * r = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rw [← Nat.card_eq_fintype_card, hF] at h
    simpa [sq] using h
  rcases mul_self_eq_one_iff.mp hr2 with h | h
  · exfalso
    apply hne
    apply Subtype.ext
    rw [← hrg, h, map_one]
    rfl
  · apply Subtype.ext
    rw [← hrg, h, map_neg, map_one]
    rfl

end Model

end CFSG.ClassicalInvolution.Q3.Q3PSL9
