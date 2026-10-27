module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Common

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

local notation "𝔽₃" => GaloisField 3 1

theorem three_eq_zero_three : (3 : 𝔽₃) = 0 := by
  have : CharP 𝔽₃ 3 := inferInstance
  exact_mod_cast CharP.cast_eq_zero 𝔽₃ 3

theorem eq_zero_or_one_or_neg_one_three (a : 𝔽₃) : a = 0 ∨ a = 1 ∨ a = -1 := by
  classical
  have : Fintype 𝔽₃ := Fintype.ofFinite _
  have hcard : Fintype.card 𝔽₃ = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact natCard_galoisField_three
  have h := FiniteField.pow_card a
  rw [hcard] at h
  have h3 : a * (a - 1) * (a + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (Or.inl (sub_eq_zero.mp h5))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h4))

theorem mul_self_ne_neg_one_three (a : 𝔽₃) : a * a ≠ -1 := by
  have h3 := three_eq_zero_three
  rcases eq_zero_or_one_or_neg_one_three a with rfl | rfl | rfl <;> intro h
  · have : (1 : 𝔽₃) = 0 := by linear_combination h
    exact one_ne_zero this
  · have : (2 : 𝔽₃) = 0 := by linear_combination h
    exact two_ne_zero_three this
  · have : (2 : 𝔽₃) = 0 := by linear_combination h
    exact two_ne_zero_three this

theorem exists_sq_add_sq_three (t : 𝔽₃) (ht : t ≠ 0) : ∃ a b : 𝔽₃, a * a + b * b = t := by
  have h3 := three_eq_zero_three
  rcases eq_zero_or_one_or_neg_one_three t with rfl | rfl | rfl
  · exact absurd rfl ht
  · exact ⟨1, 0, by ring⟩
  · exact ⟨1, 1, by linear_combination h3⟩

end CFSG.ClassicalInvolution.ModelFacts.TG3
