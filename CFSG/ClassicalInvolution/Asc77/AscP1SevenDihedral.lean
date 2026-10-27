module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalInvolution.Asc77.Thompson

section Dihedral

variable {Q : Type*} [Group Q] {a b : Q}

theorem dihedral_conj_zpow (ha : a * a = 1) (hb : b * b = 1) (i : ℤ) :
    a * (a * b) ^ i * a = (a * b) ^ (-i) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hai, mul_inv_rev, hai, hbi, ← mul_assoc, ha, one_mul]
  have h2 : (a * (a * b) * a⁻¹) ^ i = a * (a * b) ^ i * a⁻¹ := conj_zpow
  rw [h1, inv_zpow'] at h2
  rw [hai] at h2
  exact h2.symm

theorem dihedral_mul_zpow (ha : a * a = 1) (hb : b * b = 1) (i : ℤ) :
    a * (a * b) ^ i = (a * b) ^ (-i) * a := by
  calc a * (a * b) ^ i = a * (a * b) ^ i * a * a := by rw [mul_assoc (a * (a * b) ^ i) a a, ha,
        mul_one]
    _ = (a * b) ^ (-i) * a := by rw [dihedral_conj_zpow ha hb]

theorem dihedral_mem_closure (ha : a * a = 1) (hb : b * b = 1) {h : Q}
    (hh : h ∈ Subgroup.closure ({a, b} : Set Q)) :
    ∃ i : ℤ, h = (a * b) ^ i ∨ h = (a * b) ^ i * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, Or.inr (by rw [hx]; simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [hx, zpow_neg_one, mul_inv_rev, hai, hbi, mul_assoc, ha, mul_one]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, hi | hi⟩ := hx <;> obtain ⟨k, hk | hk⟩ := hy
    · exact ⟨i + k, Or.inl (by rw [hi, hk, zpow_add])⟩
    · exact ⟨i + k, Or.inr (by rw [hi, hk, zpow_add, mul_assoc])⟩
    · refine ⟨i - k, Or.inr ?_⟩
      rw [hi, hk, mul_assoc, dihedral_mul_zpow ha hb, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨i - k, Or.inl ?_⟩
      rw [hi, hk, mul_assoc, ← mul_assoc a, dihedral_conj_zpow ha hb, sub_eq_add_neg, zpow_add]
  | inv x _ hx =>
    obtain ⟨i, hi | hi⟩ := hx
    · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [hi, mul_inv_rev, hai, ← zpow_neg, dihedral_mul_zpow ha hb, neg_neg]

theorem exists_zpow_eq_one_of_conj_mem_closure (ha : a * a = 1) (hb : b * b = 1) {h : Q}
    (hh : h ∈ Subgroup.closure ({a, b} : Set Q)) (hab : h * a * h⁻¹ = b) :
    ∃ i : ℤ, (a * b) ^ (2 * i + 1) = 1 := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hb' : b = (a * b) ^ (-1 : ℤ) * a := by
    rw [zpow_neg_one, mul_inv_rev, hai, hbi, mul_assoc, ha, mul_one]
  obtain ⟨i, hi | hi⟩ := dihedral_mem_closure ha hb hh
  · refine ⟨i, ?_⟩
    have h1 : h * a * h⁻¹ = (a * b) ^ (2 * i) * a := by
      rw [hi, ← zpow_neg, mul_assoc, dihedral_mul_zpow ha hb, neg_neg, ← mul_assoc, ← zpow_add,
        two_mul]
    rw [h1] at hab
    have h2 : (a * b) ^ (2 * i) = (a * b) ^ (-1 : ℤ) :=
      mul_right_cancel (hab.trans hb')
    have : (a * b) ^ (2 * i + 1) = (a * b) ^ (2 * i) * (a * b) ^ (1 : ℤ) := zpow_add _ _ _
    rw [this, h2, ← zpow_add]
    simp
  · refine ⟨i, ?_⟩
    have h1 : h * a * h⁻¹ = (a * b) ^ (2 * i) * a := by
      rw [hi, mul_inv_rev, hai, ← zpow_neg]
      calc (a * b) ^ i * a * a * (a * (a * b) ^ (-i))
          = (a * b) ^ i * (a * a) * (a * (a * b) ^ (-i)) := by rw [mul_assoc ((a * b) ^ i) a a]
        _ = (a * b) ^ i * (a * (a * b) ^ (-i)) := by rw [ha, mul_one]
        _ = (a * b) ^ i * ((a * b) ^ (-(-i)) * a) := by rw [dihedral_mul_zpow ha hb]
        _ = (a * b) ^ (2 * i) * a := by
          rw [neg_neg, ← mul_assoc, ← zpow_add, two_mul]
    rw [h1] at hab
    have h2 : (a * b) ^ (2 * i) = (a * b) ^ (-1 : ℤ) :=
      mul_right_cancel (hab.trans hb')
    have : (a * b) ^ (2 * i + 1) = (a * b) ^ (2 * i) * (a * b) ^ (1 : ℤ) := zpow_add _ _ _
    rw [this, h2, ← zpow_add]
    simp

theorem pow_six_eq_one_of_comm (ha : a * a = 1) (hb : b * b = 1)
    (h : a * (a * b * a * b * (a * b * a)) = (a * b * a * b * (a * b * a)) * a) :
    (a * b) ^ 6 = 1 := by
  have e : a * b * a * b * (a * b * a) = (a * b) ^ 3 * a := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e] at h
  have h1 : a * (a * b) ^ 3 * a = (a * b) ^ 3 := by
    calc a * (a * b) ^ 3 * a = a * ((a * b) ^ 3 * a) := by rw [mul_assoc]
      _ = ((a * b) ^ 3 * a) * a := h
      _ = (a * b) ^ 3 := by rw [mul_assoc, ha, mul_one]
  have h2 := dihedral_conj_zpow ha hb 3
  rw [zpow_ofNat] at h2
  rw [h1] at h2
  have h3 : (a * b) ^ 6 = (a * b) ^ 3 * (a * b) ^ 3 := by rw [← pow_add]
  rw [h3]
  calc (a * b) ^ 3 * (a * b) ^ 3 = (a * b) ^ 3 * (a * b) ^ (-(3 : ℤ)) := by rw [← h2]
    _ = 1 := by rw [← zpow_natCast, ← zpow_add]; simp

theorem pow_six_eq_one_of_eq (h : a = a * b * a * b * (a * b * a)) : (a * b) ^ 6 = 1 := by
  have e : a * b * a * b * (a * b * a) = (a * b) ^ 3 * a := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e] at h
  have h3 : (a * b) ^ 3 = 1 := by
    have : (a * b) ^ 3 * a = 1 * a := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]

end Dihedral

theorem pow_three_of_odd_of_six {Q : Type*} [Group Q] {ρ : Q} {i : ℤ}
    (h1 : ρ ^ (2 * i + 1) = 1) (h6 : ρ ^ 6 = 1) : ρ ^ 3 = 1 := by
  have h6' : ρ ^ (6 : ℤ) = 1 := by exact_mod_cast h6
  have e : (3 : ℤ) = (2 * i + 1) * 3 + 6 * (-i) := by ring
  have : ρ ^ (3 : ℤ) = 1 := by
    rw [e, zpow_add, zpow_mul, zpow_mul, h1, h6', one_zpow, one_zpow, one_mul]
  exact_mod_cast this

end CFSG.ClassicalInvolution.Asc77.Thompson
