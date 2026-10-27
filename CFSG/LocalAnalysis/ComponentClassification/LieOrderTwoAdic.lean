module

public import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.RankThree.PartTwo.KFacts.OddChar

variable {q j : ℕ}

theorem padicValNat_of_mod_four_eq_one (hq1 : 1 < q) (h : q % 4 = 1) :
    2 ≤ padicValNat 2 (q - 1) ∧ padicValNat 2 (q + 1) = 1 :=
  ⟨(padicValNat_dvd_iff_le (p := 2) (n := 2) (by omega)).mp (by omega),
    padicValNat_eq_one_of_mod_four (by omega)⟩

theorem padicValNat_of_mod_four_eq_three (h : q % 4 = 3) :
    padicValNat 2 (q - 1) = 1 ∧ 2 ≤ padicValNat 2 (q + 1) :=
  ⟨padicValNat_eq_one_of_mod_four (by omega),
    (padicValNat_dvd_iff_le (p := 2) (n := 2) (by omega)).mp (by omega)⟩

theorem three_le_padicValNat_sq_sub_one (hq : Odd q) (hq1 : 1 < q) :
    3 ≤ padicValNat 2 (q ^ 2 - 1) := by
  have h0 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 two_ne_zero
  exact (padicValNat_dvd_iff_le (p := 2) (n := 3) h0).mp (by
    simpa using Nat.eight_dvd_sq_sub_one_of_odd hq)

theorem padicValNat_pow_sub_one_add_one_of_odd (hq : Odd q) (hq1 : 1 < q) (hj : Odd j) :
    padicValNat 2 (q ^ j - 1) = padicValNat 2 (q - 1) ∧
      padicValNat 2 (q ^ j + 1) = padicValNat 2 (q + 1) := by
  have hj0 : j ≠ 0 := hj.pos.ne'
  have hm : q ^ j - 1 ≠ 0 := pow_sub_one_ne_zero hq1 hj0
  have hp : q ^ j + 1 ≠ 0 := Nat.succ_ne_zero _
  have hlo1 : padicValNat 2 (q - 1) ≤ padicValNat 2 (q ^ j - 1) :=
    (padicValNat_dvd_iff_le hm).mp (pow_padicValNat_dvd.trans (Nat.sub_one_dvd_pow_sub_one q j))
  have hlo2 : padicValNat 2 (q + 1) ≤ padicValNat 2 (q ^ j + 1) :=
    (padicValNat_dvd_iff_le hp).mp (pow_padicValNat_dvd.trans (by
      simpa using Odd.nat_add_dvd_pow_add_pow q 1 hj))
  have hprod : q ^ (2 * j) - 1 = (q ^ j + 1) * (q ^ j - 1) := by
    rw [mul_comm, pow_mul, show (q ^ j) ^ 2 - 1 = (q ^ j) ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq]
  have hsum := padicValNat_pow_two_mul_sub_one hq hq1 hj0
  rw [hprod, padicValNat.mul hp hm, padicValNat_sq_sub_one hq hq1,
    padicValNat.eq_zero_of_not_dvd hj.not_two_dvd_nat] at hsum
  omega

theorem padicValNat_pow_sub_one_of_odd (hq : Odd q) (hq1 : 1 < q) (hj : Odd j) :
    padicValNat 2 (q ^ j - 1) = padicValNat 2 (q - 1) :=
  (padicValNat_pow_sub_one_add_one_of_odd hq hq1 hj).1

theorem padicValNat_pow_add_one_of_odd (hq : Odd q) (hj : Odd j) :
    padicValNat 2 (q ^ j + 1) = padicValNat 2 (q + 1) := by
  by_cases hq1 : q = 1
  · subst hq1
    simp
  · exact (padicValNat_pow_sub_one_add_one_of_odd hq (by have := hq.pos; omega) hj).2

theorem padicValNat_gcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat 2 (Nat.gcd a b) = min (padicValNat 2 a) (padicValNat 2 b) := by
  have h := congrArg (· 2) (Nat.factorization_gcd ha hb)
  simpa [Nat.factorization_def _ Nat.prime_two] using h

theorem padicValNat_gcd_of_odd_left {a : ℕ} (ha : Odd a) (b : ℕ) :
    padicValNat 2 (Nat.gcd a b) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => ha.not_two_dvd_nat (h.trans (Nat.gcd_dvd_left a b))

theorem padicValNat_gcd_three (m : ℕ) : padicValNat 2 (Nat.gcd 3 m) = 0 :=
  padicValNat_gcd_of_odd_left ⟨1, by norm_num⟩ m

theorem padicValNat_two_four : padicValNat 2 4 = 2 := by
  simpa using padicValNat.prime_pow (p := 2) 2

theorem padicValNat_gcd_four_sub_one (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (Nat.gcd 4 (q - 1)) = if q % 4 = 1 then 2 else 1 := by
  rw [padicValNat_gcd (by norm_num) (by omega), padicValNat_two_four]
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by have := Nat.odd_iff.mp hq; omega) with h | h
  · simp [h, (padicValNat_of_mod_four_eq_one hq1 h).1]
  · simp [h, (padicValNat_of_mod_four_eq_three h).1]

theorem padicValNat_gcd_four_add_one (hq : Odd q) :
    padicValNat 2 (Nat.gcd 4 (q + 1)) = if q % 4 = 3 then 2 else 1 := by
  rw [padicValNat_gcd (by norm_num) (Nat.succ_ne_zero _), padicValNat_two_four]
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by have := Nat.odd_iff.mp hq; omega) with h | h
  · simp [h, padicValNat_eq_one_of_mod_four (n := q + 1) (by omega)]
  · simp [h, (padicValNat_of_mod_four_eq_three h).2]

theorem gcd_two_sub_one (hq : Odd q) : Nat.gcd 2 (q - 1) = 2 :=
  Nat.gcd_eq_left (by have := Nat.odd_iff.mp hq; omega)

theorem padicValNat_gcd_two_sub_one (hq : Odd q) : padicValNat 2 (Nat.gcd 2 (q - 1)) = 1 := by
  rw [gcd_two_sub_one hq, padicValNat.self one_lt_two]

theorem odd_triality_factor (hq : Odd q) : Odd (q ^ 8 + q ^ 4 + 1) :=
  (hq.pow.add_odd hq.pow).add_one

theorem padicValNat_triality_factor (hq : Odd q) : padicValNat 2 (q ^ 8 + q ^ 4 + 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (odd_triality_factor hq).not_two_dvd_nat

theorem two_pow_twelve_dvd (hq : Odd q) (hq1 : 1 < q) :
    2 ^ 12 ∣ (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) := by
  have h12 : q ^ 12 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h8 : q ^ 8 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq1 (by norm_num)
  have e12 := padicValNat_pow_two_mul_sub_one hq hq1 (k := 6) (by norm_num)
  have e8 := padicValNat_pow_two_mul_sub_one hq hq1 (k := 4) (by norm_num)
  have h3 := three_le_padicValNat_sq_sub_one hq hq1
  have v6 : padicValNat 2 6 = 1 := padicValNat_eq_one_of_mod_four (by norm_num)
  have v4 := padicValNat_two_four
  refine (padicValNat_dvd_iff_le (mul_ne_zero (mul_ne_zero h12 h8) h2)).mpr ?_
  rw [padicValNat.mul (mul_ne_zero h12 h8) h2, padicValNat.mul h12 h8]
  norm_num at e12 e8
  omega

theorem three_pow_mod_eight_of_odd {f : ℕ} (hf : Odd f) : 3 ^ f % 8 = 3 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

theorem padicValNat_three_pow_sub_one_of_odd {f : ℕ} (hf : Odd f) : padicValNat 2 (3 ^ f - 1) = 1 :=
  padicValNat_eq_one_of_mod_four (by
    have := three_pow_mod_eight_of_odd hf
    have := pow_pos (by norm_num : 0 < 3) f
    omega)

theorem padicValNat_three_pow_add_one_of_odd {f : ℕ} (hf : Odd f) :
    padicValNat 2 (3 ^ f + 1) = 2 := by
  have h8 := three_pow_mod_eight_of_odd hf
  have h0 : 3 ^ f + 1 ≠ 0 := Nat.succ_ne_zero _
  have h1 : 2 ≤ padicValNat 2 (3 ^ f + 1) :=
    (padicValNat_dvd_iff_le (p := 2) (n := 2) h0).mp (by omega)
  have h2 : ¬ 3 ≤ padicValNat 2 (3 ^ f + 1) := fun h =>
    absurd ((padicValNat_dvd_iff_le (p := 2) (n := 3) h0).mpr h) (by omega)
  omega

end CFSG.ComponentClassification.CatLeafProof
