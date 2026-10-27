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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def groupAlgebraAugmentation (ring group : Type*) [CommSemiring ring]
    [Monoid group] : MonoidAlgebra ring group →+* ring :=
  (MonoidAlgebra.lift ring ring group (1 : group →* ring)).toRingHom

theorem groupAlgebraAugmentation_single {ring group : Type*} [CommSemiring ring]
    [Monoid group] (element : group) (coefficient : ring) :
    groupAlgebraAugmentation ring group (MonoidAlgebra.single element coefficient) = coefficient := by
  simp [groupAlgebraAugmentation, MonoidAlgebra.lift_single]

theorem groupAlgebra_sum_single {ring group : Type*} [Semiring ring] [Fintype group]
    (value : MonoidAlgebra ring group) :
    (∑ element : group, MonoidAlgebra.single element (value.coeff element)) = value := by
  calc
    _ = value.coeff.sum MonoidAlgebra.single := (Finsupp.sum_fintype value.coeff
      MonoidAlgebra.single (fun element => MonoidAlgebra.single_zero (R := ring) element)).symm
    _ = value := MonoidAlgebra.sum_coeff_single value

theorem groupAlgebraAugmentation_sum {ring group : Type*} [CommSemiring ring]
    [Monoid group] [Fintype group] (value : MonoidAlgebra ring group) :
    groupAlgebraAugmentation ring group value = ∑ element : group, value.coeff element := by
  conv_lhs => rw [← groupAlgebra_sum_single value]
  simp only [map_sum, groupAlgebraAugmentation_single]

theorem abelian_p_group_algebra_frobenius {field group : Type*} [Field field]
    [CommGroup group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (exponent : ℕ) (hcard : Nat.card group = prime ^ exponent)
    (value : MonoidAlgebra field group) :
    value ^ (prime ^ exponent) = MonoidAlgebra.single 1
      ((groupAlgebraAugmentation field group value) ^ (prime ^ exponent)) := by
  let := Fintype.ofFinite group
  let : ExpChar field prime := ExpChar.prime (Fact.out : prime.Prime)
  let : CharP (MonoidAlgebra field group) prime :=
    (RingHom.charP_iff_charP (algebraMap field (MonoidAlgebra field group)) prime).mp
      inferInstance
  let : ExpChar (MonoidAlgebra field group) prime := ExpChar.prime
    (Fact.out : prime.Prime)
  conv_lhs => rw [← groupAlgebra_sum_single value]
  rw [sum_pow_char_pow prime exponent]
  have hpower : ∀ element : group, element ^ (prime ^ exponent) = 1 := by
    intro element
    rw [← hcard, pow_card_eq_one']
  simp only [MonoidAlgebra.single_pow, hpower]
  rw [groupAlgebraAugmentation_sum, sum_pow_char_pow prime exponent]
  exact (map_sum (MonoidAlgebra.singleAddHom 1) _ _).symm

theorem abelian_p_group_algebra_isUnit_iff {field group : Type*} [Field field]
    [CommGroup group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (hgroup : IsPGroup prime group) (value : MonoidAlgebra field group) :
    IsUnit value ↔ groupAlgebraAugmentation field group value ≠ 0 := by
  constructor
  · intro hunit
    exact isUnit_iff_ne_zero.mp (hunit.map (groupAlgebraAugmentation field group))
  · intro hnonzero
    obtain ⟨exponent, hcard⟩ := hgroup.exists_card_eq
    have hpower : IsUnit (value ^ (prime ^ exponent)) := by
      rw [abelian_p_group_algebra_frobenius prime exponent hcard]
      have hcoefficient : IsUnit ((groupAlgebraAugmentation field group value) ^
          (prime ^ exponent)) := (isUnit_iff_ne_zero.mpr hnonzero).pow _
      exact hcoefficient.map (algebraMap field (MonoidAlgebra field group))
    exact (isUnit_pow_iff (Nat.ne_of_gt
      (Nat.pow_pos (Fact.out : prime.Prime).pos))).mp hpower

end CFSG.TwoRankLowerBound.Helpers
