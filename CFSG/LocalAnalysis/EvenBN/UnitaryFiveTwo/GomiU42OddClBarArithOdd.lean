module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarDefs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClArithC
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem u42_arith_bar_orth_odd {f m ε e : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m) (hε : ε = 1 ∨ ε = 2)
    (he : e ∣ Nat.gcd (2 * m + 1) (3 ^ f + 1)) (h : 25920 * e * ε = 2 * u42Sp (3 ^ f) m) :
    False := by
  have h25920 : (25920 : ℕ) ≠ 0 := by norm_num
  have hd1 : ¬ 3 ∣ 3 ^ f + 1 := u42_arithC_not_three_dvd hf
  have hd0 : 3 ^ f + 1 ≠ 0 := by positivity
  have he_dvd : e ∣ 3 ^ f + 1 := he.trans (Nat.gcd_dvd_right _ _)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at he_dvd
    exact hd0 he_dvd
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hu0 : u42Sp (3 ^ f) m ≠ 0 := by
    unfold u42Sp
    exact mul_ne_zero (pow_ne_zero _ (by positivity)) (u42ProdSq_ne_zero hf m)
  have hv : (25920 * e * ε).factorization 3 = (2 * u42Sp (3 ^ f) m).factorization 3 := by
    rw [h]
  have hL : (25920 * e * ε).factorization 3
      = (25920 : ℕ).factorization 3 + e.factorization 3 + ε.factorization 3 := by
    rw [Nat.factorization_mul (mul_ne_zero h25920 he0) hε0, Finsupp.add_apply,
      Nat.factorization_mul h25920 he0, Finsupp.add_apply]
  have hC : (25920 : ℕ).factorization 3 = 4 := u42_arithC_v3_C₀ (Or.inl rfl)
  have he3 : e.factorization 3 = 0 := u42_arithC_v3_zero_of_dvd hd1 he_dvd
  have hε3 : ε.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rcases hε with rfl | rfl <;> norm_num)
  have hR : (2 * u42Sp (3 ^ f) m).factorization 3 = f * m ^ 2 := by
    rw [Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) hu0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 2), zero_add,
      u42_factorization_three_u42Sp hf m]
  have hsum : 4 = f * m ^ 2 := by
    rw [hL, hC, he3, hε3, hR] at hv
    omega
  have hm2 : m ≤ 2 := by
    by_contra hc
    have h3 : 3 ≤ m := by omega
    have h1 : 1 * 3 ^ 2 ≤ f * m ^ 2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left h3 2)
    norm_num at h1
    omega
  have hm12 : m = 1 ∨ m = 2 := by omega
  rcases hm12 with rfl | rfl
  · have hf4 : f = 4 := by
      norm_num at hsum
      omega
    subst hf4
    have hV : 2 * u42Sp (3 ^ 4) 1 = 1062720 := by decide
    have hg : Nat.gcd (2 * 1 + 1) (3 ^ 4 + 1) = 1 := by norm_num
    rw [hg, Nat.dvd_one] at he
    subst he
    omega
  · have hf1 : f = 1 := by
      norm_num at hsum
      omega
    subst hf1
    have hV : 2 * u42Sp (3 ^ 1) 2 = 103680 := by decide
    have hg : Nat.gcd (2 * 2 + 1) (3 ^ 1 + 1) = 1 := by norm_num
    rw [hg, Nat.dvd_one] at he
    subst he
    omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
