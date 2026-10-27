module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

private theorem e16_arith_eight_dvd_sq_sub_one {q : ℕ} (hq : q % 4 = 1) (i : ℕ) :
    8 ∣ q ^ (2 * i) - 1 := by
  have h2 : 8 ∣ q ^ 2 - 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
    have e : (4 * k + 1) ^ 2 = 8 * (k * (2 * k + 1)) + 1 := by ring
    rw [e, Nat.add_sub_cancel]
    exact dvd_mul_right 8 _
  have h3 : q ^ 2 - 1 ∣ (q ^ 2) ^ i - 1 ^ i := Nat.sub_dvd_pow_sub_pow _ _ _
  rw [one_pow, ← pow_mul] at h3
  exact dvd_trans h2 h3

private theorem e16_arith_eight_pow_dvd_prod {q : ℕ} (hq : q % 4 = 1) (m : ℕ) :
    8 ^ m ∣ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
  have h : ∀ i ∈ Finset.Icc 1 m, (8 : ℕ) ∣ q ^ (2 * i) - 1 :=
    fun i _ => e16_arith_eight_dvd_sq_sub_one hq i
  have h2 : ∏ _i ∈ Finset.Icc 1 m, (8 : ℕ) ∣ ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) :=
    Finset.prod_dvd_prod_of_dvd _ _ h
  rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at h2
  exact h2

theorem e16_arith_psp {n q : ℕ} (hq : q % 4 = 1) (hn : 2 ≤ n) :
    2 ^ 5 * lieOrderDivisor .PSp n q ∣ lieOrderNumerator .PSp n q := by
  show (2 : ℕ) ^ 5 * Nat.gcd 2 (q - 1) ∣ q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  have hg : (2 : ℕ) ^ 5 * Nat.gcd 2 (q - 1) ∣ 2 ^ 6 :=
    dvd_trans (mul_dvd_mul_left _ (Nat.gcd_dvd_left 2 (q - 1))) (by norm_num)
  have h83 : (2 : ℕ) ^ 6 ∣ 8 ^ n := by
    have h6 : (2 : ℕ) ^ 6 = 8 ^ 2 := by norm_num
    rw [h6]
    exact pow_dvd_pow 8 hn
  have hP : (2 : ℕ) ^ 6 ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    dvd_trans h83 (e16_arith_eight_pow_dvd_prod hq n)
  exact dvd_trans hg (dvd_trans hP (dvd_mul_left _ _))

theorem e16_arith_omegaOdd {n q : ℕ} (hq : q % 4 = 1) (hn : 3 ≤ n) :
    2 ^ 5 * lieOrderDivisor .POmegaOdd n q ∣ lieOrderNumerator .POmegaOdd n q := by
  show (2 : ℕ) ^ 5 * 2 ∣ q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  have h83 : (2 : ℕ) ^ 6 ∣ 8 ^ n := by
    have h6 : (2 : ℕ) ^ 6 = 8 ^ 2 := by norm_num
    rw [h6]
    exact pow_dvd_pow 8 (by omega)
  have hP : (2 : ℕ) ^ 6 ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    dvd_trans h83 (e16_arith_eight_pow_dvd_prod hq n)
  have hg : (2 : ℕ) ^ 5 * 2 ∣ 2 ^ 6 := by norm_num
  exact dvd_trans hg (dvd_trans hP (dvd_mul_left _ _))

theorem e16_arith_omegaPlus {n q : ℕ} (hq : q % 4 = 1) (hn : 4 ≤ n) :
    2 ^ 5 * lieOrderDivisor .POmegaPlus n q ∣ lieOrderNumerator .POmegaPlus n q := by
  show (2 : ℕ) ^ 5 * Nat.gcd 4 (q ^ n - 1) ∣
    q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  have hg : (2 : ℕ) ^ 5 * Nat.gcd 4 (q ^ n - 1) ∣ 8 ^ 3 :=
    dvd_trans (mul_dvd_mul_left _ (Nat.gcd_dvd_left 4 (q ^ n - 1))) (by norm_num)
  have hP : (8 : ℕ) ^ 3 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    dvd_trans (pow_dvd_pow 8 (by omega)) (e16_arith_eight_pow_dvd_prod hq (n - 1))
  exact dvd_trans hg (dvd_trans hP (dvd_mul_left _ _))

theorem e16_arith_omegaMinus {n q : ℕ} (hq : q % 4 = 1) (hn : 4 ≤ n) :
    2 ^ 5 * lieOrderDivisor .POmegaMinus n q ∣ lieOrderNumerator .POmegaMinus n q := by
  show (2 : ℕ) ^ 5 * Nat.gcd 4 (q ^ n + 1) ∣
    q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  have hg : (2 : ℕ) ^ 5 * Nat.gcd 4 (q ^ n + 1) ∣ 8 ^ 3 :=
    dvd_trans (mul_dvd_mul_left _ (Nat.gcd_dvd_left 4 (q ^ n + 1))) (by norm_num)
  have hP : (8 : ℕ) ^ 3 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    dvd_trans (pow_dvd_pow 8 (by omega)) (e16_arith_eight_pow_dvd_prod hq (n - 1))
  exact dvd_trans hg (dvd_trans hP (dvd_mul_left _ _))

end CFSG.ComponentClassification.CatFC
