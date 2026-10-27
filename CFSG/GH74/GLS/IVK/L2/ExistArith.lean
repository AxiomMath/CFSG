module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.IVK

private theorem padicValNat_two_two_mul_odd' {m : ℕ} (hm : Odd m) : padicValNat 2 (2 * m) = 1 := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [padicValNat.mul h2 hm0, padicValNat.self (by norm_num : 1 < 2)]
  have : ¬ 2 ∣ m := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hm
    omega
  rw [padicValNat.eq_zero_of_not_dvd this]

theorem geom_sum_mul_nat (x m : ℕ) (hx : 1 ≤ x) :
    (x - 1) * ∑ i ∈ Finset.range m, x ^ i = x ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : 1 ≤ x ^ m := Nat.one_le_pow _ _ hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    generalize (y + 1) ^ m = P at h1 ⊢
    have h2 : P * (y + 1) = P * y + P := by ring
    have h3 : y * P = P * y := mul_comm _ _
    omega

theorem odd_geom_sum (x m : ℕ) (hx : Odd x) (hm : Odd m) : Odd (∑ i ∈ Finset.range m, x ^ i) := by
  rw [Nat.odd_iff]
  have h1 : (∑ i ∈ Finset.range m, x ^ i) % 2 = (∑ i ∈ Finset.range m, (x ^ i % 2)) % 2 := by
    rw [Finset.sum_nat_mod]
  rw [h1]
  have h2 : ∀ i ∈ Finset.range m, x ^ i % 2 = 1 := by
    intro i _
    exact Nat.odd_iff.mp (hx.pow)
  rw [Finset.sum_congr rfl h2]
  simp [Nat.odd_iff.mp hm]

theorem padicValNat_two_pow_sub_one_odd {x m : ℕ} (hx : Odd x) (hx1 : 1 < x) (hm : Odd m) :
    padicValNat 2 (x ^ m - 1) = padicValNat 2 (x - 1) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hS := odd_geom_sum x m hx hm
  have hS0 : (∑ i ∈ Finset.range m, x ^ i) ≠ 0 := by
    rintro h; rw [h] at hS; simp at hS
  have hx0 : x - 1 ≠ 0 := by omega
  rw [← geom_sum_mul_nat x m (by omega), padicValNat.mul hx0 hS0]
  have : ¬ 2 ∣ ∑ i ∈ Finset.range m, x ^ i := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hS
    omega
  rw [padicValNat.eq_zero_of_not_dvd this, add_zero]

theorem padicValNat_two_sq_sq_sub_one {a : ℕ} (ha : Odd a) (ha1 : 1 < a) :
    padicValNat 2 ((a ^ 2) ^ 2 - 1) = padicValNat 2 (a ^ 2 - 1) + 1 := by
  obtain ⟨k, hk⟩ := ha
  subst hk
  generalize hb : (2 * k + 1) ^ 2 = b
  have hb8 : b % 8 = 1 := by
    have h : k * (k + 1) % 2 = 0 := by
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩ <;> subst hj <;> ring_nf <;> omega
    have : b = 8 * (k * (k + 1) / 2) + 1 := by
      rw [← hb]
      nlinarith [Nat.div_add_mod (k * (k + 1)) 2]
    omega
  obtain ⟨c, hc⟩ : ∃ c, b = 8 * c + 1 := ⟨b / 8, by omega⟩
  have hb1 : 1 < b := by nlinarith
  have e3 : b ^ 2 - 1 = (b - 1) * (b + 1) := by
    obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [e3]
  have hne1 : b - 1 ≠ 0 := by omega
  rw [padicValNat.mul hne1 (by omega)]
  have hv1 : padicValNat 2 (b + 1) = 1 := by
    have : b + 1 = 2 * (4 * c + 1) := by omega
    rw [this]; exact padicValNat_two_two_mul_odd' ⟨2 * c, by omega⟩
  rw [hv1]

theorem padicValNat_card_odd {q₁ n : ℕ} (hq : Odd q₁) (hq1 : 1 < q₁) (hn : Odd n) :
    padicValNat 2 (q₁ ^ n * ((q₁ ^ n) ^ 2 - 1)) = padicValNat 2 (q₁ * (q₁ ^ 2 - 1)) := by
  have hqn : Odd (q₁ ^ n) := hq.pow
  have hqn1 : 1 < q₁ ^ n := Nat.one_lt_pow (by rintro rfl; simp at hn) hq1
  have hX0 : (q₁ ^ n) ^ 2 - 1 ≠ 0 := by
    have : 1 < (q₁ ^ n) ^ 2 := Nat.one_lt_pow (by norm_num) hqn1
    omega
  have hq20 : q₁ ^ 2 - 1 ≠ 0 := by
    have : 1 < q₁ ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hodd : ∀ {a : ℕ}, Odd a → padicValNat 2 a = 0 := by
    intro a ha
    apply padicValNat.eq_zero_of_not_dvd
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := ha
    omega
  rw [padicValNat.mul (by omega) hX0, padicValNat.mul (by omega) hq20, hodd hqn, hodd hq, zero_add,
    zero_add]
  have e1 : (q₁ ^ n) ^ 2 = (q₁ ^ 2) ^ n := by ring
  rw [e1]
  exact padicValNat_two_pow_sub_one_odd (hq.pow) (Nat.one_lt_pow (by norm_num) hq1) hn

theorem padicValNat_card_even {q₁ m : ℕ} (hq : Odd q₁) (hq1 : 1 < q₁) (hm : Odd m) :
    padicValNat 2 (((q₁ ^ (2 * m)) ^ 2) - 1) = padicValNat 2 (q₁ ^ 2 - 1) + 1 := by
  have e1 : (q₁ ^ (2 * m)) ^ 2 = ((q₁ ^ 2) ^ 2) ^ m := by ring
  rw [e1]
  have hq2 : Odd ((q₁ ^ 2) ^ 2) := (hq.pow).pow
  have hq21 : 1 < (q₁ ^ 2) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by norm_num) hq1)
  rw [padicValNat_two_pow_sub_one_odd hq2 hq21 hm]
  exact padicValNat_two_sq_sq_sub_one hq hq1

end CFSG.GH74.GLS.IVK
