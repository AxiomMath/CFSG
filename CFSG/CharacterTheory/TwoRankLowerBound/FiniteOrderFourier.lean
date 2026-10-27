module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteOrderAverages
public import Mathlib.Tactic.Polynomial.Basic

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem primitiveRoot_fourier_sum {ring : Type*} [CommRing ring] [IsDomain ring]
    (period : ℕ) (root : ringˣ) (hroot : IsPrimitiveRoot (root : ring) period)
    (exponent : ℕ) (hexponent : exponent < period) :
    (∑ label ∈ Finset.range period, (↑(root ^ label)⁻¹ : ring) ^ exponent) =
      if exponent = 0 then (period : ring) else 0 := by
  by_cases hzero : exponent = 0
  · simp [hzero]
  · rw [ite_eq_right hzero]
    let value : ring := (↑root⁻¹ : ring) ^ exponent
    have hvaluePeriod : value ^ period = 1 := by
      dsimp [value]
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      have hunitPeriod : root ^ period = 1 := by
        apply Units.ext
        exact hroot.pow_eq_one
      rw [← Units.val_pow_eq_pow_val, inv_pow, hunitPeriod]
      simp
    have hnot : value ≠ 1 := by
      intro hequal
      have hinverse : root⁻¹ ^ exponent = 1 := by
        apply Units.ext
        simpa only [value, Units.val_pow_eq_pow_val, Units.val_one] using hequal
      have hunit : root ^ exponent = 1 := by
        have hback := congrArg Inv.inv hinverse
        simpa only [inv_pow, inv_inv, inv_one] using hback
      have hdivides := hroot.dvd_of_pow_eq_one exponent
        (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hunit)
      exact hzero (Nat.eq_zero_of_dvd_of_lt hdivides hexponent)
    have hgeometric := geom_sum_mul value period
    rw [hvaluePeriod, sub_self] at hgeometric
    have hsum : (∑ label ∈ Finset.range period, value ^ label) = 0 :=
      (mul_eq_zero.mp hgeometric).resolve_right (sub_ne_zero.mpr hnot)
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro label _
    dsimp [value]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem finiteOrderEigenprojection_sum {ring algebra : Type*} [CommRing ring] [IsDomain ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit root : ringˣ)
    (hunit : (periodUnit : ring) = period) (hroot : IsPrimitiveRoot (root : ring) period)
    (operator : algebra) :
    (∑ label ∈ Finset.range period,
      finiteOrderEigenprojection period periodUnit (root ^ label) operator) = 1 := by
  have hpositive : 0 < period := by
    have hnonzero := periodUnit.ne_zero
    rw [hunit] at hnonzero
    by_contra hnot
    have hzero : period = 0 := Nat.eq_zero_of_not_pos hnot
    exact hnonzero (hzero ▸ Nat.cast_zero)
  simp only [finiteOrderEigenprojection, cyclicOperatorAverage, smul_pow]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hsum : (∑ exponent ∈ Finset.range period,
      ∑ label ∈ Finset.range period, (↑(root ^ label)⁻¹ : ring) ^ exponent • operator ^ exponent) =
        (period : ring) • (1 : algebra) := by
    simp_rw [← Finset.sum_smul]
    have hformula : ∀ exponent ∈ Finset.range period,
        (∑ label ∈ Finset.range period, (↑(root ^ label)⁻¹ : ring) ^ exponent) =
          if exponent = 0 then (period : ring) else 0 := by
      intro exponent hmember
      exact primitiveRoot_fourier_sum period root hroot exponent (Finset.mem_range.mp hmember)
    rw [Finset.sum_congr rfl (fun exponent hmember =>
      congrArg (fun coefficient : ring => coefficient • operator ^ exponent) (hformula exponent hmember))]
    simp [ite_smul, hpositive]
  rw [hsum, smul_smul, ← hunit, Units.inv_mul, one_smul]

theorem finiteOrderEigenprojection_commute {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit root : ringˣ)
    (operator other : algebra) (hcommute : Commute other operator) :
    Commute other (finiteOrderEigenprojection period periodUnit root operator) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro exponent _
  exact (hcommute.smul_right _).pow_right exponent

end CFSG.TwoRankLowerBound.Helpers
