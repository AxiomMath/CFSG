module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClBarDefs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClArithC

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem u42_arith_bar_sp {f m ε e X : ℕ} (hf : 1 ≤ f) (hm : 2 ≤ m) (hε : ε = 1 ∨ ε = 2)
    (hX : X = 25920 ∨ X = 51840) (he : e ∣ Nat.gcd (2 * m) (3 ^ f + 1))
    (h : X * e * ε = u42Sp (3 ^ f) m) : m = 2 ∧ f = 1 := by
  have hX0 : X ≠ 0 := by rcases hX with rfl | rfl <;> norm_num
  have hd1 : ¬ 3 ∣ 3 ^ f + 1 := u42_arithC_not_three_dvd hf
  have hd0 : 3 ^ f + 1 ≠ 0 := by positivity
  have he_dvd : e ∣ 3 ^ f + 1 := he.trans (Nat.gcd_dvd_right _ _)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at he_dvd
    exact hd0 he_dvd
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hv : (X * e * ε).factorization 3 = (u42Sp (3 ^ f) m).factorization 3 := by rw [h]
  have hL : (X * e * ε).factorization 3
      = X.factorization 3 + e.factorization 3 + ε.factorization 3 := by
    rw [Nat.factorization_mul (mul_ne_zero hX0 he0) hε0, Finsupp.add_apply,
      Nat.factorization_mul hX0 he0, Finsupp.add_apply]
  have hX3 : X.factorization 3 = 4 := u42_arithC_v3_C₀ hX
  have he3 : e.factorization 3 = 0 := u42_arithC_v3_zero_of_dvd hd1 he_dvd
  have hε3 : ε.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rcases hε with rfl | rfl <;> norm_num)
  have hsum : 4 = f * m ^ 2 := by
    rw [hL, hX3, he3, hε3, u42_factorization_three_u42Sp hf m] at hv
    omega
  have hm2 : m = 2 := by
    by_contra hc
    have h3 : 3 ≤ m := by omega
    have h1 : 1 * 3 ^ 2 ≤ f * m ^ 2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left h3 2)
    norm_num at h1
    omega
  refine ⟨hm2, ?_⟩
  rw [hm2] at hsum
  norm_num at hsum
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
