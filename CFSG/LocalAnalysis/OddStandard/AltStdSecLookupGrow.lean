module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.OddStandard.AltStdSec

theorem factorial_succ_div_two {m : ℕ} (hm : 2 ≤ m) :
    (m + 1).factorial / 2 = (m + 1) * (m.factorial / 2) := by
  rw [Nat.factorial_succ]
  exact Nat.mul_div_assoc _ (Nat.dvd_factorial (by norm_num) hm)

theorem sq_le_three_pow_pred {p : ℕ} (hp : 3 ≤ p) : p ^ 2 ≤ 3 ^ (p - 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 3 * n ^ 2 := by nlinarith
    have h2 : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [h2, pow_succ]
    calc (n + 1) ^ 2 ≤ 3 * n ^ 2 := h1
      _ ≤ 3 * 3 ^ (n - 1) := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (n - 1) * 3 := Nat.mul_comm _ _

theorem pow27_lt_sq_factorial_div_two {m : ℕ} (hm : 11 ≤ m) :
    27 ^ (m - 1) < (m.factorial / 2) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
    rw [factorial_succ_div_two (by omega)]
    have h2 : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [h2, pow_succ, mul_pow]
    have h3 : 27 ≤ (n + 1) ^ 2 := by nlinarith
    calc 27 ^ (n - 1) * 27 < (n.factorial / 2) ^ 2 * 27 :=
          Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ (n.factorial / 2) ^ 2 * (n + 1) ^ 2 := Nat.mul_le_mul_left _ h3
      _ = (n + 1) ^ 2 * (n.factorial / 2) ^ 2 := Nat.mul_comm _ _

theorem pow8_lt_factorial_div_two {m : ℕ} (hm : 18 ≤ m) : 8 ^ (m - 1) < m.factorial / 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
    rw [factorial_succ_div_two (by omega)]
    have h2 : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [h2, pow_succ]
    calc 8 ^ (n - 1) * 8 < (n.factorial / 2) * 8 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ (n.factorial / 2) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (n + 1) * (n.factorial / 2) := Nat.mul_comm _ _

theorem not_le_cube_two_of_valuation {M c v : ℕ} (hdvd : 2 ^ v ∣ M) (hnd : ¬ 2 ^ (c + 1) ∣ M)
    (hlt : (2 ^ c) ^ 3 < M) : ¬ M ≤ (2 ^ v) ^ 3 := by
  have hv : v ≤ c := by
    by_contra h
    exact hnd ((pow_dvd_pow 2 (by omega)).trans hdvd)
  have h1 : (2 ^ v) ^ 3 ≤ (2 ^ c) ^ 3 :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hv) 3
  omega

theorem not_le_cube_of_pow_dvd {m p v : ℕ} (hm : 11 ≤ m) (hp : p.Prime)
    (hdvd : p ^ v ∣ m.factorial / 2) : ¬ m.factorial / 2 ≤ (p ^ v) ^ 3 := by
  have := Fact.mk hp
  have hM : m.factorial / 2 ∣ m.factorial :=
    Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by omega))
  have hv : v ≤ padicValNat p m.factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero m)).mp (hdvd.trans hM)
  have hlt : (p - 1) * v < m :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hv)
      (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega))
  rcases hp.eq_two_or_odd with rfl | hodd
  · by_cases h18 : 18 ≤ m
    · intro hle
      have h1 : (2 ^ v) ^ 3 ≤ 8 ^ (m - 1) := by
        calc (2 ^ v) ^ 3 = 8 ^ v := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          _ ≤ 8 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact absurd (pow8_lt_factorial_div_two h18) (not_lt.mpr (hle.trans h1))
    · interval_cases m
      · exact not_le_cube_two_of_valuation (c := 7) hdvd (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial])
      · exact not_le_cube_two_of_valuation (c := 9) hdvd (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial])
      · exact not_le_cube_two_of_valuation (c := 9) hdvd (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial])
      · exact not_le_cube_two_of_valuation (c := 10) hdvd (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial])
      · exact not_le_cube_two_of_valuation (c := 10) hdvd (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial])
      · exact not_le_cube_two_of_valuation (c := 14) hdvd (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial])
      · exact not_le_cube_two_of_valuation (c := 14) hdvd (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial])
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    intro hle
    have h1 : (p ^ v) ^ 2 ≤ 3 ^ (m - 1) := by
      calc (p ^ v) ^ 2 = (p ^ 2) ^ v := pow_right_comm _ _ _
        _ ≤ (3 ^ (p - 1)) ^ v := Nat.pow_le_pow_left (sq_le_three_pow_pred hp3) v
        _ = 3 ^ ((p - 1) * v) := by rw [← pow_mul]
        _ ≤ 3 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (m.factorial / 2) ^ 2 ≤ 27 ^ (m - 1) := by
      calc (m.factorial / 2) ^ 2 ≤ ((p ^ v) ^ 3) ^ 2 := Nat.pow_le_pow_left hle 2
        _ = ((p ^ v) ^ 2) ^ 3 := pow_right_comm _ _ _
        _ ≤ (3 ^ (m - 1)) ^ 3 := Nat.pow_le_pow_left h1 3
        _ = 27 ^ (m - 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact absurd (pow27_lt_sq_factorial_div_two hm) (not_lt.mpr h2)

end CFSG.OddStandard.AltStdSec
