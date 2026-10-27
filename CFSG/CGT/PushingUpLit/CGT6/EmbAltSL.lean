module

public import CFSG.CGT.PushingUpLit.CGT6.SixFiveArrow

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG
open scoped Nat

theorem two_pow_lt_factorial {m : ℕ} (hm : 15 ≤ m) : 2 ^ (3 * m - 5) < m ! := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h1 : 3 * (m + 1) - 5 = (3 * m - 5) + 3 := by omega
    rw [h1, pow_add, Nat.factorial_succ]
    have h2 : 2 ^ 3 ≤ m + 1 := by omega
    calc 2 ^ (3 * m - 5) * 2 ^ 3 < m ! * 2 ^ 3 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ m ! * (m + 1) := Nat.mul_le_mul_left _ h2
      _ = (m + 1) * m ! := Nat.mul_comm _ _

theorem alt_order_eq_sl2 {m k : ℕ} (hm : 5 ≤ m) (hk : 2 ≤ k)
    (h : m ! = 2 * (2 ^ k * ((2 ^ k) ^ 2 - 1))) : m = 5 ∧ k = 2 := by
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq16 : 16 ≤ (2 ^ k) ^ 2 := by nlinarith
  have hQodd : ¬ 2 ∣ (2 ^ k) ^ 2 - 1 := by
    have h2 : 2 ∣ (2 ^ k) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    omega
  have hQne : (2 ^ k) ^ 2 - 1 ≠ 0 := by omega
  have hv : padicValNat 2 (m !) = k + 1 := by
    rw [h, padicValNat.mul (by norm_num) (mul_ne_zero (by positivity) hQne),
      padicValNat.mul (by positivity) hQne, padicValNat.self (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hQodd]
    ring
  have hlt : padicValNat 2 (m !) < m := padicValNat_factorial_lt_of_ne_zero 2 (by omega)
  have hkm : k + 2 ≤ m := by omega
  have hbig : m ! ≤ 2 ^ (3 * k + 1) := by
    rw [h]
    have h1 : (2 ^ k) ^ 2 - 1 ≤ 2 ^ (2 * k) := by
      rw [← pow_mul, mul_comm k 2]
      exact Nat.sub_le _ _
    calc 2 * (2 ^ k * ((2 ^ k) ^ 2 - 1)) ≤ 2 * (2 ^ k * 2 ^ (2 * k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = 2 ^ (3 * k + 1) := by ring
  by_cases h15 : 15 ≤ m
  · exfalso
    have h2 := two_pow_lt_factorial h15
    have h3 : 2 ^ (3 * k + 1) ≤ 2 ^ (3 * m - 5) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hm14 : m ≤ 14 := by omega
    have hk12 : k ≤ 12 := by omega
    clear hbig hv hlt hQodd hQne
    interval_cases m <;> interval_cases k <;> first | exact ⟨rfl, rfl⟩ | (exfalso; revert h; decide)

theorem alt_sl2_iso {m k : ℕ} (hm : 5 ≤ m) (hk : 2 ≤ k)
    (e : alternatingGroup (Fin m) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
    m = 5 ∧ k = 2 := by
  have h1 := Nat.card_congr e.toEquiv
  rw [natCard_alt m (by omega), CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    GaloisField.card 2 k (by omega)] at h1
  apply alt_order_eq_sl2 hm hk
  have h2 : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) (by omega)
  omega

end CFSG.CGT.PushingUpLit.CGT6
