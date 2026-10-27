module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem tri_ge_pred (x : ℕ) (hx : 2 ≤ x) : x - 1 ≤ x * (x - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  calc (x - 1) * 2 = 2 * (x - 1) := by ring
    _ ≤ x * (x - 1) := Nat.mul_le_mul_right _ hx

theorem tri_ge_self (x : ℕ) : x ≤ x * (x + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · exact Nat.mul_le_mul_left x (by omega)

theorem tri_ge_two (x : ℕ) (hx : 5 ≤ x) : 2 * x ≤ x * (x - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨t, rfl⟩ : ∃ t, x = t + 5 := ⟨x - 5, by omega⟩
  have ht : t + 5 - 1 = t + 4 := by omega
  rw [ht]
  nlinarith

theorem arithB_m1 (ℓ n e : ℕ) (he : e ≤ 1) (hn2 : 2 ≤ n) (hA : 3 ≤ ℓ + e)
    (hg : n * (2 * ℓ - 1) ≤ ℓ + e + 2) : False := by
  have h1 : 2 * (2 * ℓ - 1) ≤ n * (2 * ℓ - 1) := Nat.mul_le_mul_right _ hn2
  omega

theorem arithB_m2 (ℓ n e : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (he3 : e = 1 → 3 ≤ n) (hl2 : ℓ = 2 → 2 ≤ n)
    (hA : 3 ≤ ℓ + e) (hg : n * (2 * ℓ - 1) ≤ ℓ + e + 2) : n = 1 ∧ ℓ = 3 := by
  have h1 : 2 * ℓ - 1 ≤ n * (2 * ℓ - 1) := Nat.le_mul_of_pos_left _ hn
  have hl : ℓ ≤ 4 := by omega
  interval_cases ℓ <;> interval_cases e <;> (try norm_num at he3 hl2 hg hA ⊢) <;> omega

theorem arithC_m1 (ℓ n e : ℕ) (he : e ≤ 1) (hn2 : 2 ≤ n) (hA : 3 ≤ ℓ + e)
    (hg : n * (ℓ * (ℓ + 1) / 2) ≤ ℓ + e + 2) : False := by
  have h0 := tri_ge_self ℓ
  have h1 : 2 * (ℓ * (ℓ + 1) / 2) ≤ n * (ℓ * (ℓ + 1) / 2) := Nat.mul_le_mul_right _ hn2
  have hl : ℓ ≤ 3 := by omega
  interval_cases ℓ <;> interval_cases e <;> (try norm_num at hg hA) <;> omega

theorem arithC_m3 (ℓ n e r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hr : r ≤ ℓ / 2) (hA : 3 ≤ r + e)
    (hg : n * (ℓ * (ℓ + 1) / 2) ≤ r + e + 2) : False := by
  have h1 : ℓ * (ℓ + 1) / 2 ≤ n * (ℓ * (ℓ + 1) / 2) := Nat.le_mul_of_pos_left _ hn
  have hl : 4 ≤ ℓ := by omega
  have h2 : 2 * ℓ ≤ ℓ * (ℓ + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  omega

theorem arithB_m3 (ℓ n e r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hr : r ≤ ℓ / 2) (hA : 3 ≤ r + e)
    (hg : n * (2 * ℓ - 1) ≤ r + e + 2) : False := by
  have h1 : 2 * ℓ - 1 ≤ n * (2 * ℓ - 1) := Nat.le_mul_of_pos_left _ hn
  have hl : 4 ≤ ℓ := by omega
  omega

theorem arithD_m1 (ℓ n e b : ℕ) (he : e ≤ 1) (hb : b ≤ 1) (hb4 : b = 1 → ℓ = 4) (hn2 : 2 ≤ n)
    (he3 : e = 1 → 3 ≤ n) (hℓ : 3 ≤ ℓ) (hA : 3 ≤ ℓ + e + b)
    (hg : n * (ℓ * (ℓ - 1) / 2) ≤ ℓ + e + b + 2) : False := by
  have h0 := tri_ge_pred ℓ (by omega)
  have h1 : 2 * (ℓ * (ℓ - 1) / 2 ) ≤ n * (ℓ * (ℓ - 1) / 2) := Nat.mul_le_mul_right _ hn2
  have hl : ℓ ≤ 7 := by omega
  interval_cases ℓ <;> interval_cases e <;> interval_cases b <;> (try norm_num at hb4 he3 hg hA ⊢) <;> omega

theorem arithD_m2 (ℓ n e b r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hb : b ≤ 1) (hb4 : b = 1 → ℓ = 4)
    (he3 : e = 1 → 3 ≤ n) (hℓ : 3 ≤ ℓ) (hr : (ℓ % 2 = 0 → r = ℓ) ∧ (ℓ % 2 = 1 → r + 1 = ℓ))
    (hA : 3 ≤ r + e + b) (hg : n * (ℓ * (ℓ - 1) / 2) ≤ r + e + b + 2) : n = 1 ∧ ℓ = 4 := by
  have hl : ℓ ≤ 4 := by
    by_contra hc
    have h0 := tri_ge_two ℓ (by omega)
    have h1 : ℓ * (ℓ - 1) / 2 ≤ n * (ℓ * (ℓ - 1) / 2) := Nat.le_mul_of_pos_left _ hn
    omega
  interval_cases ℓ <;> interval_cases e <;> interval_cases b <;> (try norm_num at hb4 he3 hr hg hA ⊢) <;> omega

theorem arithD_m3 (ℓ n e r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hr : r ≤ ℓ / 2) (hℓ : 3 ≤ ℓ) (hA : 3 ≤ r + e)
    (hg : n * (ℓ * (ℓ - 1) / 2) ≤ r + e + 2) : False := by
  have h1 : ℓ * (ℓ - 1) / 2 ≤ n * (ℓ * (ℓ - 1) / 2) := Nat.le_mul_of_pos_left _ hn
  have hl : 4 ≤ ℓ := by omega
  by_cases h5 : 5 ≤ ℓ
  · have h2 := tri_ge_two ℓ h5
    omega
  · have hl4 : ℓ = 4 := by omega
    subst hl4
    norm_num at hg
    omega

theorem arithTD_m1 (ℓ n e : ℕ) (he : e ≤ 1) (hn2 : 2 ≤ n) (hA : 3 ≤ ℓ - 1 + e)
    (hg : n * (2 * ℓ - 2) ≤ ℓ - 1 + e + 2) : False := by
  have h1 : 2 * (2 * ℓ - 2) ≤ n * (2 * ℓ - 2) := Nat.mul_le_mul_right _ hn2
  omega

theorem arithTD_m2 (ℓ n e r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (he3 : e = 1 → 3 ≤ n) (hℓ : 2 ≤ ℓ)
    (hr : (ℓ % 2 = 0 → r + 1 = ℓ) ∧ (ℓ % 2 = 1 → r = ℓ))
    (hA : 3 ≤ r + e) (hg : n * (2 * ℓ - 2) ≤ r + e + 2) : n = 1 ∧ ℓ = 3 := by
  have hl : ℓ ≤ 5 := by
    by_contra hc
    have h1 : 2 * ℓ - 2 ≤ n * (2 * ℓ - 2) := Nat.le_mul_of_pos_left _ hn
    omega
  interval_cases ℓ <;> interval_cases e <;> (try norm_num at he3 hr hg hA ⊢) <;> omega

theorem arithTD_m3 (ℓ n e r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hr : r ≤ ℓ / 2) (hℓ : 2 ≤ ℓ) (hA : 3 ≤ r + e)
    (hg : n * (2 * ℓ - 2) ≤ r + e + 2) : False := by
  have h1 : 2 * ℓ - 2 ≤ n * (2 * ℓ - 2) := Nat.le_mul_of_pos_left _ hn
  omega

end CFSG.LocalAnalysis.GLTheoremA

end
