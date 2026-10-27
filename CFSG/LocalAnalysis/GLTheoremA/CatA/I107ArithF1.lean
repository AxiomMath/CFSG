module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem sq_div4_ge' (x : ℕ) : 2 * x - 3 ≤ (x + 1) ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases Nat.lt_or_ge x 3 with h | h
  · interval_cases x <;> norm_num
  · have h3 : 2 * x - 3 + 3 = 2 * x := by omega
    nlinarith [sq_nonneg ((x : ℤ) - 3)]

theorem arithA_m1 (ℓ n e : ℕ) (he : e ≤ 1) (hn2 : 2 ≤ n) (he3 : e = 1 → 3 ≤ n)
    (hA : 3 ≤ ℓ + e) (hg : n * ((ℓ + 1) ^ 2 / 4) ≤ ℓ + e + 2) : False := by
  have hl : ℓ ≤ 3 := by
    by_contra hc
    have h1 : 2 * ((ℓ + 1) ^ 2 / 4) ≤ n * ((ℓ + 1) ^ 2 / 4) := Nat.mul_le_mul_right _ hn2
    have h2 : 2 * (2 * ℓ - 3) ≤ 2 * ((ℓ + 1) ^ 2 / 4) := Nat.mul_le_mul_left 2 (sq_div4_ge' ℓ)
    omega
  interval_cases ℓ <;> interval_cases e <;> (try norm_num at hA hg)
  all_goals omega

theorem arithA_m2 (ℓ n e : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (he3 : e = 1 → 3 ≤ n)
    (hA : 3 ≤ (ℓ + 1) / 2 + e) (hg : n * ((ℓ + 1) ^ 2 / 4) ≤ (ℓ + 1) / 2 + e + 2) : False := by
  have hl : ℓ ≤ 4 := by
    by_contra hc
    have h1 : (ℓ + 1) ^ 2 / 4 ≤ n * ((ℓ + 1) ^ 2 / 4) := Nat.le_mul_of_pos_left _ hn
    have h2 : 2 * ℓ - 3 ≤ (ℓ + 1) ^ 2 / 4 := sq_div4_ge' ℓ
    omega
  interval_cases ℓ <;> interval_cases e <;> (try norm_num at hA hg he3)
  all_goals omega

theorem arithA_m3 (ℓ n e r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hr : r ≤ (ℓ + 1) / 3)
    (hA : 3 ≤ r + e) (hg : n * ((ℓ + 1) ^ 2 / 4) ≤ r + e + 2) : False := by
  have h1 : (ℓ + 1) ^ 2 / 4 ≤ n * ((ℓ + 1) ^ 2 / 4) := Nat.le_mul_of_pos_left _ hn
  have h2 : 2 * ℓ - 3 ≤ (ℓ + 1) ^ 2 / 4 := sq_div4_ge' ℓ
  omega

theorem arithT_m1 (ℓ n e : ℕ) (he : e ≤ 1) (hn2 : 2 ≤ n) (he3 : e = 1 → 3 ≤ n)
    (hA : 3 ≤ (ℓ + 1) / 2 + e) (hg : n * ((ℓ + 1) / 2) ^ 2 ≤ (ℓ + 1) / 2 + e + 2) : False := by
  have hs : (ℓ + 1) / 2 ≤ 2 := by
    by_contra hc
    have hc3 : 3 ≤ (ℓ + 1) / 2 := by omega
    have hq3 : 3 * ((ℓ + 1) / 2) ≤ ((ℓ + 1) / 2) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul_right _ hc3
    have hq1 : ((ℓ + 1) / 2) ^ 2 ≤ n * ((ℓ + 1) / 2) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hs2 : (ℓ + 1) / 2 = 2 := by omega
  rw [hs2] at hg hA
  have hn' : n * 4 ≤ 5 := by norm_num at hg; omega
  interval_cases e <;> (try norm_num at he3) <;> omega

theorem arithT_m2 (ℓ n e : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (he3 : e = 1 → 3 ≤ n ∧ n ≠ 4 ∧ n ≠ 5) (hl2 : 2 ≤ ℓ)
    (hl2' : ℓ = 2 → 2 ≤ n) (hA : 3 ≤ ℓ + e) (hg : n * ((ℓ + 1) / 2) ^ 2 ≤ ℓ + e + 2) :
    (n = 1 ∧ (ℓ = 3 ∨ ℓ = 4)) ∨ (ℓ = 2 ∧ n = 3 ∧ e = 1) := by
  have hl : ℓ ≤ 6 := by
    by_contra hc
    have hs : 4 ≤ (ℓ + 1) / 2 := by omega
    have hq4 : 4 * ((ℓ + 1) / 2) ≤ ((ℓ + 1) / 2) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul_right _ hs
    have hq1 : ((ℓ + 1) / 2) ^ 2 ≤ n * ((ℓ + 1) / 2) ^ 2 := Nat.le_mul_of_pos_left _ hn
    omega
  interval_cases ℓ <;> interval_cases e <;> (try norm_num at hg hA he3 hl2' ⊢)
  all_goals omega

theorem arithT_m3 (ℓ n e r : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hr : r ≤ (ℓ + 1) / 3)
    (hA : 3 ≤ r + e) (hg : n * ((ℓ + 1) / 2) ^ 2 ≤ r + e + 2) : False := by
  have hs : 3 ≤ (ℓ + 1) / 2 := by omega
  have hq3 : 3 * ((ℓ + 1) / 2) ≤ ((ℓ + 1) / 2) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul_right _ hs
  have hq1 : ((ℓ + 1) / 2) ^ 2 ≤ n * ((ℓ + 1) / 2) ^ 2 := Nat.le_mul_of_pos_left _ hn
  have ht : (ℓ + 1) / 3 ≤ (ℓ + 1) / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)
  omega

end CFSG.LocalAnalysis.GLTheoremA

end
