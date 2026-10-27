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

theorem finite_prime_primary_factorization {G : Type*} [Group G] [Finite G]
    (element : G) (prime : ℕ) (hprime : Nat.Prime prime) :
    ∃ (primary regular : G) (exponent : ℕ), primary ∈ Subgroup.zpowers element ∧
      regular ∈ Subgroup.zpowers element ∧ Commute primary regular ∧ primary * regular = element ∧
      orderOf primary ∣ prime ^ exponent ∧ Nat.Coprime prime (orderOf regular) := by
  let exponent := (orderOf element).factorization prime
  let primePower := prime ^ exponent
  let complement := orderOf element / primePower
  have hnonzero : orderOf element ≠ 0 := (orderOf_pos element).ne'
  have hprimeComplement : Nat.Coprime prime complement := Nat.coprime_ordCompl hprime hnonzero
  have hcoprime : Nat.Coprime primePower complement := hprimeComplement.pow_left exponent
  have hproduct : primePower * complement = orderOf element := by
    exact Nat.mul_div_cancel' (Nat.ordProj_dvd (orderOf element) prime)
  let firstExponent : ℤ := (primePower : ℤ) * Nat.gcdA primePower complement
  let secondExponent : ℤ := (complement : ℤ) * Nat.gcdB primePower complement
  have hsum : firstExponent + secondExponent = 1 := by
    have hbezout := Nat.gcd_eq_gcd_ab primePower complement
    rw [hcoprime.gcd_eq_one, Nat.cast_one] at hbezout
    exact hbezout.symm
  let regular := element ^ firstExponent
  let primary := element ^ secondExponent
  have hregularPower : regular ^ complement = 1 := by
    change (element ^ firstExponent) ^ complement = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hequal : firstExponent * (complement : ℤ) =
        (orderOf element : ℤ) * Nat.gcdA primePower complement := by
      rw [← hproduct, Nat.cast_mul]
      dsimp [firstExponent]
      ring
    rw [hequal, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hprimaryPower : primary ^ primePower = 1 := by
    change (element ^ secondExponent) ^ primePower = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hequal : secondExponent * (primePower : ℤ) =
        (orderOf element : ℤ) * Nat.gcdB primePower complement := by
      rw [← hproduct, Nat.cast_mul]
      dsimp [secondExponent]
      ring
    rw [hequal, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨primary, regular, exponent, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.zpow_mem_zpowers element secondExponent
  · exact Subgroup.zpow_mem_zpowers element firstExponent
  · exact zpow_mul_comm element secondExponent firstExponent
  · change element ^ secondExponent * element ^ firstExponent = element
    rw [← zpow_add, add_comm, hsum, zpow_one]
  · exact orderOf_dvd_of_pow_eq_one hprimaryPower
  · exact hprimeComplement.of_dvd_right (orderOf_dvd_of_pow_eq_one hregularPower)

end CFSG.TwoRankLowerBound.Helpers
