module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddArithB

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Open

theorem gomiOddD_sq_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  zify [Nat.one_le_pow 2 q hq, hq]
  ring

theorem gomiOddD_not_dvd {a : ℕ} (ha : a ≤ 7) {o : ℕ} (ho : Odd o) :
    ¬ 2 ^ 8 ∣ 2 ^ a * o := by
  intro h
  have h1 : 2 ^ a * 2 ^ (8 - a) ∣ 2 ^ a * o := by
    rw [← pow_add, show a + (8 - a) = 8 by omega]
    exact h
  have h2 : 2 ^ (8 - a) ∣ o := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
  have h3 : 2 ∣ o := (dvd_pow_self 2 (by omega)).trans h2
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h3)

theorem gomiOddD_ordA_three_eq (q : ℕ) :
    ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q - 1) := by
  simp [ordA, Finset.prod_Icc_succ_top, mul_assoc]

theorem gomiOddD_ordA_three_one {q j : ℕ} (hq : q = 8 * j + 1) : 2 ^ 9 ∣ ordA 3 q := by
  rw [gomiOddD_ordA_three_eq]
  have hq1 : 1 ≤ q := by omega
  have hqodd : Odd q := ⟨4 * j, by omega⟩
  have e1 : q - 1 = 8 * j := by omega
  have h3 : 8 ∣ q ^ 3 - 1 := by
    have := gomiOdd_sub_one_dvd_pow_sub_one q 3
    rw [e1] at this
    exact (Dvd.intro j rfl).trans this
  have h2 : 16 ∣ q ^ 2 - 1 := by
    rw [gomiOddD_sq_sub_one q hq1, e1]
    exact ⟨j * (4 * j + 1), by rw [hq]; ring⟩
  have h4 := gomiOdd_sixteen_dvd_pow_four_sub_one hqodd
  have hX : 2 ^ (9 + 2) ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
    refine Dvd.dvd.mul_left ?_ _
    have : 16 * 8 * 16 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) :=
      mul_dvd_mul (mul_dvd_mul h2 h3) h4
    exact Dvd.dvd.trans (by norm_num) this
  exact gomiOdd_pow_dvd_div_of_dvd_two_pow (by simpa using Nat.gcd_dvd_left 4 (q - 1)) hX

theorem gomiOddD_ordA_three_three {q j : ℕ} (hq : q = 8 * j + 3) : ¬ 2 ^ 8 ∣ ordA 3 q := by
  rw [gomiOddD_ordA_three_eq]
  have e2 : q ^ 2 - 1 = 8 * ((4 * j + 1) * (2 * j + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 - 1 = 2 * ((4 * j + 1) * (q ^ 2 + q + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e4 : q ^ 4 - 1 = 16 * ((4 * j + 1) * (2 * j + 1) * (32 * j ^ 2 + 24 * j + 5)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have hg : Nat.gcd 4 (q - 1) = 2 := by
    have : (q - 1) % 4 = 2 := by omega
    rw [Nat.gcd_rec 4 (q - 1), this]
    decide
  have hqodd : Odd q := ⟨4 * j + 1, by omega⟩
  have hodd : Odd (q ^ 6 * (4 * j + 1) ^ 3 * (2 * j + 1) ^ 2 * (q ^ 2 + q + 1) *
      (32 * j ^ 2 + 24 * j + 5)) := by
    have h1 : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
    have h2 : Odd (2 * j + 1) := ⟨j, rfl⟩
    have h3 : Odd (q ^ 2 + q + 1) := by
      subst hq; exact ⟨32 * j ^ 2 + 28 * j + 6, by ring⟩
    have h4 : Odd (32 * j ^ 2 + 24 * j + 5) := ⟨16 * j ^ 2 + 12 * j + 2, by ring⟩
    exact (((hqodd.pow.mul h1.pow).mul h2.pow).mul h3).mul h4
  have hX : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) =
      2 * (2 ^ 7 * (q ^ 6 * (4 * j + 1) ^ 3 * (2 * j + 1) ^ 2 * (q ^ 2 + q + 1) *
        (32 * j ^ 2 + 24 * j + 5))) := by
    rw [e2, e3, e4]; ring
  rw [hg, hX, Nat.mul_div_cancel_left _ (by norm_num)]
  exact gomiOddD_not_dvd (by norm_num) hodd

theorem gomiOddD_ordA_three_five {q j : ℕ} (hq : q = 8 * j + 5) : ¬ 2 ^ 8 ∣ ordA 3 q := by
  rw [gomiOddD_ordA_three_eq]
  have e2 : q ^ 2 - 1 = 8 * ((2 * j + 1) * (4 * j + 3)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 - 1 = 4 * ((2 * j + 1) * (q ^ 2 + q + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e4 : q ^ 4 - 1 = 16 * ((2 * j + 1) * (4 * j + 3) * (32 * j ^ 2 + 40 * j + 13)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have hg : Nat.gcd 4 (q - 1) = 4 := by
    have : (q - 1) % 4 = 0 := by omega
    rw [Nat.gcd_rec 4 (q - 1), this]
    decide
  have hqodd : Odd q := ⟨4 * j + 2, by omega⟩
  have hodd : Odd (q ^ 6 * (2 * j + 1) ^ 3 * (4 * j + 3) ^ 2 * (q ^ 2 + q + 1) *
      (32 * j ^ 2 + 40 * j + 13)) := by
    have h1 : Odd (2 * j + 1) := ⟨j, rfl⟩
    have h2 : Odd (4 * j + 3) := ⟨2 * j + 1, by ring⟩
    have h3 : Odd (q ^ 2 + q + 1) := by
      subst hq; exact ⟨32 * j ^ 2 + 44 * j + 15, by ring⟩
    have h4 : Odd (32 * j ^ 2 + 40 * j + 13) := ⟨16 * j ^ 2 + 20 * j + 6, by ring⟩
    exact (((hqodd.pow.mul h1.pow).mul h2.pow).mul h3).mul h4
  have hX : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) =
      4 * (2 ^ 7 * (q ^ 6 * (2 * j + 1) ^ 3 * (4 * j + 3) ^ 2 * (q ^ 2 + q + 1) *
        (32 * j ^ 2 + 40 * j + 13))) := by
    rw [e2, e3, e4]; ring
  rw [hg, hX, Nat.mul_div_cancel_left _ (by norm_num)]
  exact gomiOddD_not_dvd (by norm_num) hodd

theorem gomiOddD_ordA_three_seven {q j : ℕ} (hq : q = 8 * j + 7) : 2 ^ 9 ∣ ordA 3 q := by
  rw [gomiOddD_ordA_three_eq]
  have e2 : q ^ 2 - 1 = 16 * ((4 * j + 3) * (j + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 - 1 = 2 * ((4 * j + 3) * (q ^ 2 + q + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e4 : q ^ 4 - 1 = 32 * ((4 * j + 3) * (j + 1) * (32 * j ^ 2 + 56 * j + 25)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have hg : Nat.gcd 4 (q - 1) = 2 := by
    have : (q - 1) % 4 = 2 := by omega
    rw [Nat.gcd_rec 4 (q - 1), this]
    decide
  have hX : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) =
      2 * (2 ^ 9 * (q ^ 6 * (4 * j + 3) ^ 3 * (j + 1) ^ 2 * (q ^ 2 + q + 1) *
        (32 * j ^ 2 + 56 * j + 25))) := by
    rw [e2, e3, e4]; ring
  rw [hg, hX, Nat.mul_div_cancel_left _ (by norm_num)]
  exact Dvd.intro _ rfl

theorem gomiOdd_ordA_three {q : ℕ} (hq : Odd q) (h8 : 2 ^ 8 ∣ ordA 3 q) : 2 ^ 9 ∣ ordA 3 q := by
  obtain ⟨k, hk⟩ := hq
  have hr : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  rcases hr with h | h | h | h
  · exact gomiOddD_ordA_three_one (j := q / 8) (by omega)
  · exact absurd h8 (gomiOddD_ordA_three_three (j := q / 8) (by omega))
  · exact absurd h8 (gomiOddD_ordA_three_five (j := q / 8) (by omega))
  · exact gomiOddD_ordA_three_seven (j := q / 8) (by omega)

theorem gomiOddD_ordTwistedA_three_eq (q : ℕ) :
    ordTwistedA 3 q =
      q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q + 1) := by
  simp [ordTwistedA, Finset.prod_Icc_succ_top, gomiOddB_natCast_pow_toNat,
    gomiOddB_natCast_pow_add_one_toNat, mul_assoc]

theorem gomiOddD_ordTwistedA_three_one {q j : ℕ} (hq : q = 8 * j + 1) :
    2 ^ 9 ∣ ordTwistedA 3 q := by
  rw [gomiOddD_ordTwistedA_three_eq]
  have e2 : q ^ 2 - 1 = 16 * (j * (4 * j + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 + 1 = 2 * ((4 * j + 1) * (64 * j ^ 2 + 8 * j + 1)) := by
    subst hq; ring
  have e4 : q ^ 4 - 1 = 32 * (j * (4 * j + 1) * (32 * j ^ 2 + 8 * j + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have hg : Nat.gcd 4 (q + 1) = 2 := by
    have : (q + 1) % 4 = 2 := by omega
    rw [Nat.gcd_rec 4 (q + 1), this]
    decide
  have hX : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) =
      2 * (2 ^ 9 * (q ^ 6 * j ^ 2 * (4 * j + 1) ^ 3 * (64 * j ^ 2 + 8 * j + 1) *
        (32 * j ^ 2 + 8 * j + 1))) := by
    rw [e2, e3, e4]; ring
  rw [hg, hX, Nat.mul_div_cancel_left _ (by norm_num)]
  exact Dvd.intro _ rfl

theorem gomiOddD_ordTwistedA_three_three {q j : ℕ} (hq : q = 8 * j + 3) :
    ¬ 2 ^ 8 ∣ ordTwistedA 3 q := by
  rw [gomiOddD_ordTwistedA_three_eq]
  have e2 : q ^ 2 - 1 = 8 * ((4 * j + 1) * (2 * j + 1)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 + 1 = 4 * ((2 * j + 1) * (64 * j ^ 2 + 40 * j + 7)) := by
    subst hq; ring
  have e4 : q ^ 4 - 1 = 16 * ((4 * j + 1) * (2 * j + 1) * (32 * j ^ 2 + 24 * j + 5)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have hg : Nat.gcd 4 (q + 1) = 4 := by
    have : (q + 1) % 4 = 0 := by omega
    rw [Nat.gcd_rec 4 (q + 1), this]
    decide
  have hqodd : Odd q := ⟨4 * j + 1, by omega⟩
  have hodd : Odd (q ^ 6 * (4 * j + 1) ^ 2 * (2 * j + 1) ^ 3 * (64 * j ^ 2 + 40 * j + 7) *
      (32 * j ^ 2 + 24 * j + 5)) := by
    have h1 : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
    have h2 : Odd (2 * j + 1) := ⟨j, rfl⟩
    have h3 : Odd (64 * j ^ 2 + 40 * j + 7) := ⟨32 * j ^ 2 + 20 * j + 3, by ring⟩
    have h4 : Odd (32 * j ^ 2 + 24 * j + 5) := ⟨16 * j ^ 2 + 12 * j + 2, by ring⟩
    exact (((hqodd.pow.mul h1.pow).mul h2.pow).mul h3).mul h4
  have hX : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) =
      4 * (2 ^ 7 * (q ^ 6 * (4 * j + 1) ^ 2 * (2 * j + 1) ^ 3 * (64 * j ^ 2 + 40 * j + 7) *
        (32 * j ^ 2 + 24 * j + 5))) := by
    rw [e2, e3, e4]; ring
  rw [hg, hX, Nat.mul_div_cancel_left _ (by norm_num)]
  exact gomiOddD_not_dvd (by norm_num) hodd

theorem gomiOddD_ordTwistedA_three_five {q j : ℕ} (hq : q = 8 * j + 5) :
    ¬ 2 ^ 8 ∣ ordTwistedA 3 q := by
  rw [gomiOddD_ordTwistedA_three_eq]
  have e2 : q ^ 2 - 1 = 8 * ((2 * j + 1) * (4 * j + 3)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 + 1 = 2 * ((4 * j + 3) * (64 * j ^ 2 + 72 * j + 21)) := by
    subst hq; ring
  have e4 : q ^ 4 - 1 = 16 * ((2 * j + 1) * (4 * j + 3) * (32 * j ^ 2 + 40 * j + 13)) := by
    subst hq; apply Nat.sub_eq_of_eq_add; ring
  have hg : Nat.gcd 4 (q + 1) = 2 := by
    have : (q + 1) % 4 = 2 := by omega
    rw [Nat.gcd_rec 4 (q + 1), this]
    decide
  have hqodd : Odd q := ⟨4 * j + 2, by omega⟩
  have hodd : Odd (q ^ 6 * (2 * j + 1) ^ 2 * (4 * j + 3) ^ 3 * (64 * j ^ 2 + 72 * j + 21) *
      (32 * j ^ 2 + 40 * j + 13)) := by
    have h1 : Odd (2 * j + 1) := ⟨j, rfl⟩
    have h2 : Odd (4 * j + 3) := ⟨2 * j + 1, by ring⟩
    have h3 : Odd (64 * j ^ 2 + 72 * j + 21) := ⟨32 * j ^ 2 + 36 * j + 10, by ring⟩
    have h4 : Odd (32 * j ^ 2 + 40 * j + 13) := ⟨16 * j ^ 2 + 20 * j + 6, by ring⟩
    exact (((hqodd.pow.mul h1.pow).mul h2.pow).mul h3).mul h4
  have hX : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) =
      2 * (2 ^ 7 * (q ^ 6 * (2 * j + 1) ^ 2 * (4 * j + 3) ^ 3 * (64 * j ^ 2 + 72 * j + 21) *
        (32 * j ^ 2 + 40 * j + 13))) := by
    rw [e2, e3, e4]; ring
  rw [hg, hX, Nat.mul_div_cancel_left _ (by norm_num)]
  exact gomiOddD_not_dvd (by norm_num) hodd

theorem gomiOddD_ordTwistedA_three_seven {q j : ℕ} (hq : q = 8 * j + 7) :
    2 ^ 9 ∣ ordTwistedA 3 q := by
  rw [gomiOddD_ordTwistedA_three_eq]
  have hq1 : 1 ≤ q := by omega
  have hqodd : Odd q := ⟨4 * j + 3, by omega⟩
  have e1 : q + 1 = 8 * (j + 1) := by omega
  have h3 : 8 ∣ q ^ 3 + 1 := by
    have := gomiOdd_add_one_dvd_pow_add_one q (by decide : Odd 3)
    rw [e1] at this
    exact (Dvd.intro (j + 1) rfl).trans this
  have h2 : 16 ∣ q ^ 2 - 1 := by
    rw [gomiOddD_sq_sub_one q hq1]
    have e0 : q - 1 = 2 * (4 * j + 3) := by omega
    rw [e0, e1]
    exact ⟨(4 * j + 3) * (j + 1), by ring⟩
  have h4 := gomiOdd_sixteen_dvd_pow_four_sub_one hqodd
  have hX : 2 ^ (9 + 2) ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
    refine Dvd.dvd.mul_left ?_ _
    have : 16 * 8 * 16 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) :=
      mul_dvd_mul (mul_dvd_mul h2 h3) h4
    exact Dvd.dvd.trans (by norm_num) this
  exact gomiOdd_pow_dvd_div_of_dvd_two_pow (by simpa using Nat.gcd_dvd_left 4 (q + 1)) hX

theorem gomiOdd_ordTwistedA_three {q : ℕ} (hq : Odd q) (h8 : 2 ^ 8 ∣ ordTwistedA 3 q) :
    2 ^ 9 ∣ ordTwistedA 3 q := by
  obtain ⟨k, hk⟩ := hq
  have hr : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  rcases hr with h | h | h | h
  · exact gomiOddD_ordTwistedA_three_one (j := q / 8) (by omega)
  · exact absurd h8 (gomiOddD_ordTwistedA_three_three (j := q / 8) (by omega))
  · exact absurd h8 (gomiOddD_ordTwistedA_three_five (j := q / 8) (by omega))
  · exact gomiOddD_ordTwistedA_three_seven (j := q / 8) (by omega)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
