module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

private theorem e16_arith_sq_mod_eight {q : ℕ} (hq : q % 4 = 1) : q ^ 2 % 8 = 1 := by
  have h8 : q % 8 = 1 ∨ q % 8 = 5 := by omega
  rw [Nat.pow_mod]
  rcases h8 with h | h <;> simp [h]

private theorem e16_arith_pow_two_mul_mod_eight {q : ℕ} (hq : q % 4 = 1) (k : ℕ) :
    q ^ (2 * k) % 8 = 1 := by
  rw [pow_mul, Nat.pow_mod, e16_arith_sq_mod_eight hq, one_pow]
  norm_num

private theorem e16_arith_eight_dvd_pow_two_mul {q : ℕ} (hq : q % 4 = 1) (k : ℕ) :
    8 ∣ q ^ (2 * k) - 1 := by
  have := e16_arith_pow_two_mul_mod_eight hq k
  omega

private theorem e16_arith_eight_dvd_two {q : ℕ} (hq : q % 4 = 1) : 8 ∣ q ^ 2 - 1 :=
  e16_arith_eight_dvd_pow_two_mul hq 1

private theorem e16_arith_eight_dvd_six {q : ℕ} (hq : q % 4 = 1) : 8 ∣ q ^ 6 - 1 :=
  e16_arith_eight_dvd_pow_two_mul hq 3

private theorem e16_arith_eight_dvd_eight {q : ℕ} (hq : q % 4 = 1) : 8 ∣ q ^ 8 - 1 :=
  e16_arith_eight_dvd_pow_two_mul hq 4

private theorem e16_arith_two_pow_five_dvd_mul {a b : ℕ} (ha : 8 ∣ a) (hb : 8 ∣ b) :
    2 ^ 5 ∣ a * b := by
  have h : 2 ^ 5 ∣ 8 * 8 := ⟨2, by norm_num⟩
  exact Nat.dvd_trans h (mul_dvd_mul ha hb)

private theorem e16_arith_two_pow_five_mul_two_dvd_mul {a b : ℕ} (ha : 8 ∣ a) (hb : 8 ∣ b) :
    2 ^ 5 * 2 ∣ a * b := by
  have h : 2 ^ 5 * 2 ∣ 8 * 8 := ⟨1, by norm_num⟩
  exact Nat.dvd_trans h (mul_dvd_mul ha hb)

private theorem e16_arith_sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  have := Nat.sub_dvd_pow_sub_pow q 1 2
  rwa [one_pow] at this

private theorem e16_arith_mul_dvd_of_dvd_three {g N : ℕ} (hg : g ∣ 3) (h2 : 2 ^ 5 ∣ N)
    (hgN : g ∣ N) : 2 ^ 5 * g ∣ N :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.coprime_dvd_right hg (by norm_num)) h2 hgN

private theorem e16_arith_mul_dvd_of_dvd_two {g N : ℕ} (hg : g ∣ 2) (h : 2 ^ 5 * 2 ∣ N) :
    2 ^ 5 * g ∣ N :=
  Nat.dvd_trans (mul_dvd_mul_left (2 ^ 5) hg) h

theorem e16_arith_G2 {n q : ℕ} (hq : q % 4 = 1) :
    2 ^ 5 * lieOrderDivisor .G2 n q ∣ lieOrderNumerator .G2 n q := by
  have hd : lieOrderDivisor .G2 n q = 1 := rfl
  have hN : lieOrderNumerator .G2 n q = q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    simp only [lieOrderNumerator, mul_assoc]
  rw [hd, hN, mul_one]
  exact Dvd.dvd.mul_left (e16_arith_two_pow_five_dvd_mul (e16_arith_eight_dvd_six hq)
    (e16_arith_eight_dvd_two hq)) _

theorem e16_arith_F4 {n q : ℕ} (hq : q % 4 = 1) :
    2 ^ 5 * lieOrderDivisor .F4 n q ∣ lieOrderNumerator .F4 n q := by
  have hd : lieOrderDivisor .F4 n q = 1 := rfl
  have hN : lieOrderNumerator .F4 n q =
      (q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1)) * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    simp only [lieOrderNumerator, mul_assoc]
  rw [hd, hN, mul_one]
  exact Dvd.dvd.mul_left (e16_arith_two_pow_five_dvd_mul (e16_arith_eight_dvd_six hq)
    (e16_arith_eight_dvd_two hq)) _

theorem e16_arith_E6 {n q : ℕ} (hq : q % 4 = 1) :
    2 ^ 5 * lieOrderDivisor .E6 n q ∣ lieOrderNumerator .E6 n q := by
  have hd : lieOrderDivisor .E6 n q = Nat.gcd 3 (q - 1) := rfl
  have hN : lieOrderNumerator .E6 n q =
      (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 5 - 1)) *
        ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    simp only [lieOrderNumerator]
    ring
  have h2 : 2 ^ 5 ∣ lieOrderNumerator .E6 n q := by
    rw [hN]
    exact Dvd.dvd.mul_left (e16_arith_two_pow_five_dvd_mul (e16_arith_eight_dvd_six hq)
      (e16_arith_eight_dvd_two hq)) _
  have hgN : Nat.gcd 3 (q - 1) ∣ lieOrderNumerator .E6 n q := by
    rw [hN]
    exact Nat.dvd_trans (Nat.dvd_trans (Nat.gcd_dvd_right 3 (q - 1))
      (e16_arith_sub_one_dvd_sq_sub_one q)) (Dvd.dvd.mul_left (dvd_mul_left _ _) _)
  rw [hd]
  exact e16_arith_mul_dvd_of_dvd_three (Nat.gcd_dvd_left 3 (q - 1)) h2 hgN

theorem e16_arith_E7 {n q : ℕ} (hq : q % 4 = 1) :
    2 ^ 5 * lieOrderDivisor .E7 n q ∣ lieOrderNumerator .E7 n q := by
  have hd : lieOrderDivisor .E7 n q = Nat.gcd 2 (q - 1) := rfl
  have hN : lieOrderNumerator .E7 n q =
      (q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1)) *
        ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    simp only [lieOrderNumerator, mul_assoc]
  have h2 : 2 ^ 5 * 2 ∣ lieOrderNumerator .E7 n q := by
    rw [hN]
    exact Dvd.dvd.mul_left (e16_arith_two_pow_five_mul_two_dvd_mul (e16_arith_eight_dvd_six hq)
      (e16_arith_eight_dvd_two hq)) _
  rw [hd]
  exact e16_arith_mul_dvd_of_dvd_two (Nat.gcd_dvd_left 2 (q - 1)) h2

theorem e16_arith_E8 {n q : ℕ} (hq : q % 4 = 1) :
    2 ^ 5 * lieOrderDivisor .E8 n q ∣ lieOrderNumerator .E8 n q := by
  have hd : lieOrderDivisor .E8 n q = 1 := rfl
  have hN : lieOrderNumerator .E8 n q =
      (q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
        (q ^ 12 - 1)) * ((q ^ 8 - 1) * (q ^ 2 - 1)) := by
    simp only [lieOrderNumerator, mul_assoc]
  rw [hd, hN, mul_one]
  exact Dvd.dvd.mul_left (e16_arith_two_pow_five_dvd_mul (e16_arith_eight_dvd_eight hq)
    (e16_arith_eight_dvd_two hq)) _

theorem e16_arith_twistedE6 {n q : ℕ} (hq : q % 4 = 1) :
    2 ^ 5 * lieOrderDivisor .twistedE6 n q ∣ lieOrderNumerator .twistedE6 n q := by
  have hd : lieOrderDivisor .twistedE6 n q = Nat.gcd 3 (q + 1) := rfl
  have hN : lieOrderNumerator .twistedE6 n q =
      (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 5 + 1)) *
        ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    simp only [lieOrderNumerator]
    ring
  have h2 : 2 ^ 5 ∣ lieOrderNumerator .twistedE6 n q := by
    rw [hN]
    exact Dvd.dvd.mul_left (e16_arith_two_pow_five_dvd_mul (e16_arith_eight_dvd_six hq)
      (e16_arith_eight_dvd_two hq)) _
  have h5 : q + 1 ∣ q ^ 5 + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow q 1 (n := 5) (by decide)
    rwa [one_pow] at this
  have hgN : Nat.gcd 3 (q + 1) ∣ lieOrderNumerator .twistedE6 n q := by
    rw [hN]
    exact Nat.dvd_trans (Nat.dvd_trans (Nat.gcd_dvd_right 3 (q + 1)) h5)
      (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  rw [hd]
  exact e16_arith_mul_dvd_of_dvd_three (Nat.gcd_dvd_left 3 (q + 1)) h2 hgN

theorem e16_arith_trialityD4 {n q : ℕ} (hq : q % 4 = 1) :
    2 ^ 5 * lieOrderDivisor .trialityD4 n q ∣ lieOrderNumerator .trialityD4 n q := by
  have hd : lieOrderDivisor .trialityD4 n q = 1 := rfl
  have hN : lieOrderNumerator .trialityD4 n q =
      (q ^ 12 * (q ^ 8 + q ^ 4 + 1)) * ((q ^ 6 - 1) * (q ^ 2 - 1)) := by
    simp only [lieOrderNumerator, mul_assoc]
  rw [hd, hN, mul_one]
  exact Dvd.dvd.mul_left (e16_arith_two_pow_five_dvd_mul (e16_arith_eight_dvd_six hq)
    (e16_arith_eight_dvd_two hq)) _

end CFSG.ComponentClassification.CatFC
