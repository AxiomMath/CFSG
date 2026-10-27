module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def cyclicOperatorAverage {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit : ringˣ)
    (operator : algebra) : algebra :=
  (↑periodUnit⁻¹ : ring) • ∑ exponent ∈ Finset.range period, operator ^ exponent

theorem finiteOrder_geometric_sum_fixes_right {algebra : Type*} [Ring algebra]
    (period : ℕ) (operator : algebra) (hperiod : operator ^ period = 1) :
    (∑ exponent ∈ Finset.range period, operator ^ exponent) * operator =
      ∑ exponent ∈ Finset.range period, operator ^ exponent := by
  have hgeometric := geom_sum_mul operator period
  rw [hperiod, sub_self, mul_sub, mul_one] at hgeometric
  exact sub_eq_zero.mp hgeometric

theorem cyclicOperatorAverage_commute {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit : ringˣ)
    (operator : algebra) : Commute operator (cyclicOperatorAverage period periodUnit operator) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro exponent _
  exact Commute.refl operator |>.pow_right exponent

theorem cyclicOperatorAverage_fixes_right {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit : ringˣ)
    (operator : algebra) (hperiod : operator ^ period = 1) :
    cyclicOperatorAverage period periodUnit operator * operator =
      cyclicOperatorAverage period periodUnit operator := by
  rw [cyclicOperatorAverage, smul_mul_assoc, finiteOrder_geometric_sum_fixes_right period operator hperiod]

theorem cyclicOperatorAverage_fixes_left {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit : ringˣ)
    (operator : algebra) (hperiod : operator ^ period = 1) :
    operator * cyclicOperatorAverage period periodUnit operator =
      cyclicOperatorAverage period periodUnit operator := by
  rw [(cyclicOperatorAverage_commute period periodUnit operator).eq]
  exact cyclicOperatorAverage_fixes_right period periodUnit operator hperiod

theorem cyclicOperatorAverage_fixes_powers {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit : ringˣ)
    (operator : algebra) (hperiod : operator ^ period = 1) (exponent : ℕ) :
    operator ^ exponent * cyclicOperatorAverage period periodUnit operator =
      cyclicOperatorAverage period periodUnit operator := by
  induction exponent with
  | zero => simp
  | succ exponent hinduction =>
    rw [pow_succ', mul_assoc, hinduction,
      cyclicOperatorAverage_fixes_left period periodUnit operator hperiod]

theorem cyclicOperatorAverage_idempotent {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit : ringˣ)
    (hunit : (periodUnit : ring) = period) (operator : algebra)
    (hperiod : operator ^ period = 1) :
    IsIdempotentElem (cyclicOperatorAverage period periodUnit operator) := by
  change cyclicOperatorAverage period periodUnit operator * cyclicOperatorAverage period periodUnit operator = _
  calc
    _ = (↑periodUnit⁻¹ : ring) • ∑ exponent ∈ Finset.range period,
        operator ^ exponent * cyclicOperatorAverage period periodUnit operator := by
      conv_lhs => lhs; rw [cyclicOperatorAverage]
      rw [smul_mul_assoc, Finset.sum_mul]
    _ = (↑periodUnit⁻¹ : ring) • (period • cyclicOperatorAverage period periodUnit operator) := by
      simp only [cyclicOperatorAverage_fixes_powers period periodUnit operator hperiod,
        Finset.sum_const, Finset.card_range]
    _ = cyclicOperatorAverage period periodUnit operator := by
      rw [← Nat.cast_smul_eq_nsmul ring, smul_smul, ← hunit, Units.inv_mul, one_smul]

@[expose] noncomputable def finiteOrderEigenprojection {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit eigenvalue : ringˣ)
    (operator : algebra) : algebra :=
  cyclicOperatorAverage period periodUnit ((↑eigenvalue⁻¹ : ring) • operator)

theorem eigenvalueNormalizedOperator_period {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (eigenvalue : ringˣ)
    (heigenvalue : eigenvalue ^ period = 1) (operator : algebra)
    (hperiod : operator ^ period = 1) :
    ((↑eigenvalue⁻¹ : ring) • operator) ^ period = 1 := by
  rw [smul_pow, hperiod]
  have hscalar : (↑eigenvalue⁻¹ : ring) ^ period = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, heigenvalue]
    rfl
  rw [hscalar, one_smul]

theorem finiteOrderEigenprojection_idempotent {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit eigenvalue : ringˣ)
    (hunit : (periodUnit : ring) = period) (heigenvalue : eigenvalue ^ period = 1)
    (operator : algebra) (hperiod : operator ^ period = 1) :
    IsIdempotentElem (finiteOrderEigenprojection period periodUnit eigenvalue operator) :=
  cyclicOperatorAverage_idempotent period periodUnit hunit _
    (eigenvalueNormalizedOperator_period period eigenvalue heigenvalue operator hperiod)

theorem finiteOrderEigenprojection_eigenvalue {ring algebra : Type*} [CommRing ring]
    [Ring algebra] [Algebra ring algebra] (period : ℕ) (periodUnit eigenvalue : ringˣ)
    (heigenvalue : eigenvalue ^ period = 1) (operator : algebra)
    (hperiod : operator ^ period = 1) :
    operator * finiteOrderEigenprojection period periodUnit eigenvalue operator =
      (eigenvalue : ring) • finiteOrderEigenprojection period periodUnit eigenvalue operator := by
  have hfix := cyclicOperatorAverage_fixes_left period periodUnit
    ((↑eigenvalue⁻¹ : ring) • operator)
    (eigenvalueNormalizedOperator_period period eigenvalue heigenvalue operator hperiod)
  have hscaled := congrArg (fun value : algebra => (eigenvalue : ring) • value) hfix
  simpa only [smul_mul_assoc, smul_smul, Units.mul_inv, one_smul,
    finiteOrderEigenprojection] using hscaled

end CFSG.TwoRankLowerBound.Helpers
