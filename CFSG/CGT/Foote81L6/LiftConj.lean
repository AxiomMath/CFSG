module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

variable {C : Type*} [Group C] {z : C}

theorem isConj_or_isConj_mul_of_isConj_mk (hz : z ∈ center C) (hz2 : z ^ 2 = 1)
    [(zpowers z).Normal] {g h : C}
    (hgh : IsConj (QuotientGroup.mk g : C ⧸ zpowers z) (QuotientGroup.mk h)) :
    IsConj g h ∨ IsConj g (h * z) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hgh
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at hc
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hc
  have hz' : ∀ x : C, x * z = z * x := fun x => (mem_center_iff.1 hz x)
  have hzz : z * z = 1 := by rw [← sq, hz2]
  have hk2 : z ^ k = 1 ∨ z ^ k = z := by
    rw [zpow_eq_zpow_emod' k hz2]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
  rcases hk2 with h1 | hzk
  · left
    rw [h1] at hk
    refine isConj_iff.2 ⟨c, ?_⟩
    have := congrArg (fun x => c * g * c⁻¹ * x) hk.symm
    simpa [mul_assoc] using this.symm
  · right
    rw [hzk] at hk
    refine isConj_iff.2 ⟨c, ?_⟩
    have h2 : h = c * g * c⁻¹ * z := by
      have := congrArg (fun x => c * g * c⁻¹ * x) hk
      simpa [mul_assoc] using this.symm
    rw [h2, mul_assoc (c * g * c⁻¹), hzz, mul_one]

theorem not_isConj_mk_of_orderOf_ne (hz : z ∈ center C) (hz2 : z ^ 2 = 1)
    [(zpowers z).Normal] {g h : C} (h1 : orderOf g ≠ orderOf h)
    (h2 : orderOf g ≠ orderOf (h * z)) :
    ¬ IsConj (QuotientGroup.mk g : C ⧸ zpowers z) (QuotientGroup.mk h) := by
  intro hgh
  rcases isConj_or_isConj_mul_of_isConj_mk hz hz2 hgh with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact h1 (SemiconjBy.orderOf_eq _ hc)
  · exact h2 (SemiconjBy.orderOf_eq _ hc)

end CFSG.CGT.Foote81L6
