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
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

abbrev ComplexAlgebraicIntegers := ↥(integralClosure ℤ ℂ)

theorem complexAlgebraicIntegers_integral : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := by
  constructor
  exact integralClosure.isIntegral

theorem complexAlgebraicIntegers_maximal_residue_characteristic
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] :
    ∃ prime : ℕ, Nat.Prime prime ∧ CharP (ComplexAlgebraicIntegers ⧸ ideal) prime ∧
      ∀ integer : ℤ, (integer : ComplexAlgebraicIntegers) ∈ ideal ↔ (prime : ℤ) ∣ integer := by
  let : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
  let contraction := Ideal.comap (algebraMap ℤ ComplexAlgebraicIntegers) ideal
  let : contraction.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal ideal
  have hnonzero : contraction ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int contraction
  obtain hzero | ⟨prime, hprime, hspan⟩ :=
    Ideal.isPrime_int_iff.mp (inferInstance : contraction.IsPrime)
  · exact False.elim (hnonzero hzero)
  · have hmembership : ∀ integer : ℤ,
        (integer : ComplexAlgebraicIntegers) ∈ ideal ↔ (prime : ℤ) ∣ integer := by
      intro integer
      change integer ∈ contraction ↔ _
      rw [hspan, Ideal.mem_span_singleton]
    have hcharacteristic : CharP (ComplexAlgebraicIntegers ⧸ ideal) prime := by
      constructor
      intro natural
      rw [← map_natCast (Ideal.Quotient.mk ideal), Ideal.Quotient.eq_zero_iff_mem]
      have hequal := hmembership (natural : ℤ)
      simpa only [Int.cast_natCast, Int.natCast_dvd_natCast] using hequal
    exact ⟨prime, hprime, hcharacteristic, hmembership⟩

theorem rootOfUnity_mem_complexAlgebraicIntegers (root : ℂ) (exponent : ℕ)
    (hpositive : 0 < exponent) (hroot : root ^ exponent = 1) :
    root ∈ integralClosure ℤ ℂ := by
  rw [mem_integralClosure_iff]
  apply (IsIntegral.pow_iff (R := ℤ) hpositive).mp
  rw [hroot]
  exact isIntegral_one

theorem prime_power_root_residue_one (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (root : ComplexAlgebraicIntegers) (exponent : ℕ) (hroot : root ^ (prime ^ exponent) = 1) :
    root - 1 ∈ ideal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, map_one]
  have hpower : (Ideal.Quotient.mk ideal root - 1) ^ (prime ^ exponent) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hroot, map_one, one_pow, sub_self]
  exact eq_zero_of_pow_eq_zero hpower

end CFSG.TwoRankLowerBound.Helpers
