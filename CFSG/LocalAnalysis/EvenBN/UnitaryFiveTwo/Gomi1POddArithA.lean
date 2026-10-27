module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddBase
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Open

theorem gomiOddArithA_eight_dvd_pow_six_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 6 - 1 :=
  (gomiOdd_eight_dvd_sq_sub_one hq).trans (by simpa using gomiOdd_sq_sub_one_dvd_pow_two_mul q 3)

theorem gomiOddArithA_sixteen_dvd_pow_eight_sub_one {q : ℕ} (hq : Odd q) : 16 ∣ q ^ 8 - 1 :=
  (gomiOdd_sixteen_dvd_pow_four_sub_one hq).trans
    (by simpa using gomiOdd_pow_four_sub_one_dvd_pow_four_mul q 2)

theorem gomiOddArithA_eight_dvd_pow_twelve_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 12 - 1 :=
  (gomiOdd_eight_dvd_sq_sub_one hq).trans (by simpa using gomiOdd_sq_sub_one_dvd_pow_two_mul q 6)

theorem gomiOddArithA_three_factors_dvd_prod {q m : ℕ} (hm : 3 ≤ m) :
    (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) ∣ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
  have hsub : Finset.Icc 1 3 ⊆ Finset.Icc 1 m := Finset.Icc_subset_Icc le_rfl hm
  have := Finset.prod_dvd_prod_of_subset (Finset.Icc 1 3) (Finset.Icc 1 m)
    (fun i => q ^ (2 * i) - 1) hsub
  simpa [Finset.prod_Icc_succ_top, mul_assoc] using this

theorem gomiOddArithA_two_pow_ten_dvd_prod {q m : ℕ} (hq : Odd q) (hm : 3 ≤ m) :
    2 ^ 10 ∣ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
  have h3 : 8 * 16 * 8 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) :=
    mul_dvd_mul (mul_dvd_mul (gomiOdd_eight_dvd_sq_sub_one hq)
      (gomiOdd_sixteen_dvd_pow_four_sub_one hq)) (gomiOddArithA_eight_dvd_pow_six_sub_one hq)
  exact (dvd_of_eq (by norm_num : (2 : ℕ) ^ 10 = 8 * 16 * 8)).trans
    (h3.trans (gomiOddArithA_three_factors_dvd_prod hm))

theorem gomiOddArithA_two_pow_ten_dvd_three {q : ℕ} (hq : Odd q) :
    2 ^ 10 ∣ (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) :=
  (dvd_of_eq (by norm_num : (2 : ℕ) ^ 10 = 8 * 8 * 16)).trans
    (mul_dvd_mul (mul_dvd_mul (gomiOdd_eight_dvd_sq_sub_one hq)
      (gomiOddArithA_eight_dvd_pow_six_sub_one hq))
      (gomiOddArithA_sixteen_dvd_pow_eight_sub_one hq))

theorem gomiOddArithA_two_pow_ten_dvd_three' {q : ℕ} (hq : Odd q) :
    2 ^ 10 ∣ (q ^ 2 - 1) * (q ^ 8 - 1) * (q ^ 12 - 1) :=
  (dvd_of_eq (by norm_num : (2 : ℕ) ^ 10 = 8 * 16 * 8)).trans
    (mul_dvd_mul (mul_dvd_mul (gomiOdd_eight_dvd_sq_sub_one hq)
      (gomiOddArithA_sixteen_dvd_pow_eight_sub_one hq))
      (gomiOddArithA_eight_dvd_pow_twelve_sub_one hq))

theorem gomiOddArithA_add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨0, by norm_num⟩
  · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    exact ⟨m, Nat.sub_eq_of_eq_add (by ring)⟩

theorem gomiOddArithA_odd_gcd_three (m : ℕ) : Odd (Nat.gcd 3 m) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 m) with h | h <;>
    rw [h] <;> decide

theorem gomiOddArithA_two_pow_nine_dvd_div_gcd_four {E A P : ℕ} (hA : 2 ∣ A) (hP : 2 ^ 10 ∣ P) :
    2 ^ 9 ∣ E * A * P / Nat.gcd 4 A := by
  refine gomiOdd_pow_dvd_div_of_dvd_two_pow (e := 2) ?_ ?_
  · exact (Nat.gcd_dvd_left 4 A).trans (dvd_of_eq (by norm_num))
  · have hAP : 2 * 2 ^ 10 ∣ A * P := mul_dvd_mul hA hP
    have hX : A * P ∣ E * A * P := Dvd.intro E (by ring)
    exact (dvd_of_eq (by norm_num : (2 : ℕ) ^ (9 + 2) = 2 * 2 ^ 10)).trans (hAP.trans hX)

theorem gomiOdd_two_pow_nine_dvd_ordD {n q : ℕ} (hq : Odd q) (hn : 4 ≤ n) : 2 ^ 9 ∣ ordD n q := by
  unfold ordD
  exact gomiOddArithA_two_pow_nine_dvd_div_gcd_four (gomiOdd_two_dvd_pow_sub_one hq n)
    (gomiOddArithA_two_pow_ten_dvd_prod hq (by omega))

theorem gomiOdd_two_pow_nine_dvd_ordTwistedD {n q : ℕ} (hq : Odd q) (hn : 4 ≤ n) :
    2 ^ 9 ∣ ordTwistedD n q := by
  unfold ordTwistedD
  exact gomiOddArithA_two_pow_nine_dvd_div_gcd_four (gomiOdd_two_dvd_pow_add_one hq n)
    (gomiOddArithA_two_pow_ten_dvd_prod hq (by omega))

theorem gomiOdd_two_pow_nine_dvd_ordF4 {q : ℕ} (hq : Odd q) : 2 ^ 9 ∣ ordF4 q := by
  unfold ordF4
  exact (pow_dvd_pow (2 : ℕ) (by norm_num : 9 ≤ 10)).trans
    ((gomiOddArithA_two_pow_ten_dvd_three hq).trans
      (Dvd.intro (q ^ 24 * (q ^ 12 - 1)) (by ring)))

theorem gomiOdd_two_pow_nine_dvd_ordE6 {q : ℕ} (hq : Odd q) : 2 ^ 9 ∣ ordE6 q := by
  unfold ordE6
  refine gomiOdd_pow_dvd_div_of_odd ?_ (gomiOddArithA_odd_gcd_three (q - 1)) ?_
  · exact (Nat.gcd_dvd_right 3 (q - 1)).trans
      ((gomiOdd_sub_one_dvd_pow_sub_one q 2).trans (dvd_mul_left _ _))
  · exact (pow_dvd_pow (2 : ℕ) (by norm_num : 9 ≤ 10)).trans
      ((gomiOddArithA_two_pow_ten_dvd_three hq).trans
        (Dvd.intro (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 5 - 1)) (by ring)))

theorem gomiOdd_two_pow_nine_dvd_ordTwistedE6 {q : ℕ} (hq : Odd q) :
    2 ^ 9 ∣ ordTwistedE6 q := by
  unfold ordTwistedE6
  refine gomiOdd_pow_dvd_div_of_odd ?_ (gomiOddArithA_odd_gcd_three (q + 1)) ?_
  · exact (Nat.gcd_dvd_right 3 (q + 1)).trans
      ((gomiOddArithA_add_one_dvd_sq_sub_one q).trans (dvd_mul_left _ _))
  · exact (pow_dvd_pow (2 : ℕ) (by norm_num : 9 ≤ 10)).trans
      ((gomiOddArithA_two_pow_ten_dvd_three hq).trans
        (Dvd.intro (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 5 + 1)) (by ring)))

theorem gomiOdd_two_pow_nine_dvd_ordE7 {q : ℕ} (hq : Odd q) : 2 ^ 9 ∣ ordE7 q := by
  unfold ordE7
  refine gomiOdd_pow_dvd_div_of_dvd_two_pow (e := 1) ?_ ?_
  · exact (Nat.gcd_dvd_left 2 (q - 1)).trans (dvd_of_eq (by norm_num))
  · exact (gomiOddArithA_two_pow_ten_dvd_three hq).trans
      (Dvd.intro (q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1)) (by ring))

theorem gomiOdd_two_pow_nine_dvd_ordE8 {q : ℕ} (hq : Odd q) : 2 ^ 9 ∣ ordE8 q := by
  unfold ordE8
  exact (pow_dvd_pow (2 : ℕ) (by norm_num : 9 ≤ 10)).trans
    ((gomiOddArithA_two_pow_ten_dvd_three' hq).trans
      (Dvd.intro (q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
        (q ^ 14 - 1)) (by ring)))

theorem gomiOddArithA_three_pow_mod_eight (k : ℕ) : 3 ^ (2 * k + 1) % 8 = 3 := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    have h : 3 ^ (2 * (m + 1) + 1) = 3 ^ (2 * m + 1) * 9 := by ring
    show 3 ^ (2 * (m + 1) + 1) % 8 = 3
    rw [h]
    omega

theorem gomiOddArithA_mul_mod_sixteen {q : ℕ} (hq : q % 8 = 3) :
    ((q ^ 3 + 1) * (q - 1)) % 16 = 8 := by
  have hr : q % 16 = 3 ∨ q % 16 = 11 := by omega
  have hpow : q ^ 3 % 16 = (q % 16) ^ 3 % 16 := Nat.pow_mod q 3 16
  have e1 : (q ^ 3 + 1) % 16 = ((q % 16) ^ 3 % 16 + 1) % 16 := by omega
  have e2 : (q - 1) % 16 = (q % 16 + 15) % 16 := by omega
  rw [Nat.mul_mod, e1, e2]
  rcases hr with hr | hr <;> norm_num [hr]

theorem gomiOddArithA_not_two_pow_eight_dvd {Y : ℕ} (hY : Y % 16 = 8) : ¬ 2 ^ 8 ∣ Y := by
  rintro ⟨c, rfl⟩
  omega

theorem gomiOdd_not_two_pow_eight_dvd_ordRee {f : ℕ} (hf : Odd f) : ¬ 2 ^ 8 ∣ ordRee (3 ^ f) := by
  intro h
  obtain ⟨k, rfl⟩ := hf
  unfold ordRee at h
  have hodd : Odd (3 ^ (2 * k + 1) : ℕ) := (by decide : Odd (3 : ℕ)).pow
  have hcop : Nat.Coprime (2 ^ 8) ((3 ^ (2 * k + 1)) ^ 3) :=
    Nat.Coprime.pow_left 8 (Nat.coprime_two_left.mpr hodd.pow)
  rw [mul_assoc] at h
  exact gomiOddArithA_not_two_pow_eight_dvd
    (gomiOddArithA_mul_mod_sixteen (gomiOddArithA_three_pow_mod_eight k))
    (hcop.dvd_of_dvd_mul_left h)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
