module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarDefs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClArithC

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem u42_arith_bar_orth_even_minus {f m ε e : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hε : ε = 1 ∨ ε = 2) (he : e ∣ Nat.gcd (2 * (m + 1)) (3 ^ f + 1))
    (h : 25920 * e * ε = u42OEvenMinus (3 ^ f) m) : False := by
  have hd0 : 3 ^ f + 1 ≠ 0 := by positivity
  have he_dvd : e ∣ 3 ^ f + 1 := he.trans (Nat.gcd_dvd_right _ _)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at he_dvd
    exact hd0 he_dvd
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hv : (25920 * e * ε).factorization 3 = (u42OEvenMinus (3 ^ f) m).factorization 3 := by
    rw [h]
  have hL : (25920 * e * ε).factorization 3
      = (25920 : ℕ).factorization 3 + e.factorization 3 + ε.factorization 3 := by
    rw [Nat.factorization_mul (mul_ne_zero (by norm_num : (25920 : ℕ) ≠ 0) he0) hε0,
      Finsupp.add_apply, Nat.factorization_mul (by norm_num : (25920 : ℕ) ≠ 0) he0,
      Finsupp.add_apply]
  have hC : (25920 : ℕ).factorization 3 = 4 := u42_arithC_v3_C₀ (Or.inl rfl)
  have he3 : e.factorization 3 = 0 :=
    u42_arithC_v3_zero_of_dvd (u42_arithC_not_three_dvd hf) he_dvd
  have hε3 : ε.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rcases hε with rfl | rfl <;> norm_num)
  have hsum : 4 = f * (m * (m + 1)) := by
    rw [hL, hC, he3, hε3, u42_factorization_three_u42OEvenMinus hf m] at hv
    omega
  have hm1 : m = 1 := by
    by_contra hne
    have hm2 : 2 ≤ m := by omega
    have h6 : 2 * 3 ≤ m * (m + 1) := Nat.mul_le_mul hm2 (by omega)
    have h7 : 1 * (2 * 3) ≤ f * (m * (m + 1)) := Nat.mul_le_mul hf h6
    omega
  subst hm1
  have hf2 : f = 2 := by omega
  subst hf2
  have hV : u42OEvenMinus (3 ^ 2) 1 = 1062720 := by decide
  have h' : 25920 * e * ε = 1062720 := h.trans hV
  have he2 : e ∣ 2 := by
    have hg : Nat.gcd (2 * (1 + 1)) (3 ^ 2 + 1) = 2 := by norm_num
    rwa [hg] at he
  have he_le : e ≤ 2 := Nat.le_of_dvd (by norm_num) he2
  rcases hε with rfl | rfl <;> omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
