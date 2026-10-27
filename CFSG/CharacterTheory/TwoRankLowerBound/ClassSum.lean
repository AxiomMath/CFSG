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
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

open scoped BigOperators

namespace CFSG.TwoRankLowerBound.Helpers

theorem representation_invariant_sum_commutes {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ G vector)
    (support : Finset G) (hinvariant : ∀ conjugator element : G,
      element ∈ support ↔ conjugator * element * conjugator⁻¹ ∈ support)
    (conjugator : G) :
    Commute (∑ element ∈ support, representation element) (representation conjugator) := by
  classical
  have hsum : ∑ element ∈ support, representation (conjugator * element * conjugator⁻¹) =
      ∑ element ∈ support, representation element := by
    apply Finset.sum_bijective (MulAut.conj conjugator) (MulAut.conj conjugator).bijective
    · intro element
      exact hinvariant conjugator element
    · intro element _
      rfl
  change (∑ element ∈ support, representation element) * representation conjugator =
    representation conjugator * (∑ element ∈ support, representation element)
  calc
    (∑ element ∈ support, representation element) * representation conjugator =
        (∑ element ∈ support, representation (conjugator * element * conjugator⁻¹)) *
          representation conjugator := by rw [hsum]
    _ = ∑ element ∈ support,
        representation (conjugator * element * conjugator⁻¹) * representation conjugator :=
      Finset.sum_mul _ _ _
    _ = ∑ element ∈ support, representation conjugator * representation element := by
      apply Finset.sum_congr rfl
      intro element _
      rw [← map_mul]
      have hequal : conjugator * element * conjugator⁻¹ * conjugator = conjugator * element := by group
      rw [hequal, map_mul]
    _ = representation conjugator * ∑ element ∈ support, representation element :=
      (Finset.mul_sum _ _ _).symm

theorem irreducible_invariant_sum_is_scalar {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (support : Finset G) (hinvariant : ∀ conjugator element : G,
      element ∈ support ↔ conjugator * element * conjugator⁻¹ ∈ support) :
    ∃ scalar : ℂ, (∑ element ∈ support, representation element) =
      scalar • (1 : Module.End ℂ vector) := by
  let intertwiner : representation.IntertwiningMap representation :=
    { toLinearMap := ∑ element ∈ support, representation element
      isIntertwining' := fun conjugator =>
        representation_invariant_sum_commutes representation support hinvariant conjugator }
  obtain ⟨scalar, hscalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 intertwiner
  refine ⟨scalar, ?_⟩
  have hequal := congrArg Representation.IntertwiningMap.toLinearMap hscalar
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at hequal
  have hone : (1 : representation.IntertwiningMap representation).toLinearMap =
      (1 : Module.End ℂ vector) := by
    ext element
    exact congrFun (Representation.IntertwiningMap.coe_one representation) element
  rw [hone] at hequal
  exact hequal.symm

theorem irreducible_conjugacy_class_sum {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (representative : G) (support : Finset G)
    (hinvariant : ∀ conjugator element : G,
      element ∈ support ↔ conjugator * element * conjugator⁻¹ ∈ support)
    (hconjugate : ∀ element ∈ support, IsConj representative element)
    (hdegree : representation.character 1 ≠ 0) :
    (∑ element ∈ support, representation element) =
      ((support.card : ℂ) * representation.character representative / representation.character 1) •
        (1 : Module.End ℂ vector) := by
  obtain ⟨scalar, hscalar⟩ := irreducible_invariant_sum_is_scalar representation support hinvariant
  have htrace : scalar * representation.character 1 =
      support.card * representation.character representative := by
    have hequal := congrArg (LinearMap.trace ℂ vector) hscalar
    rw [map_sum, map_smul, LinearMap.trace_one, ← Representation.char_one representation] at hequal
    have hconstant : ∑ element ∈ support, representation.character element =
        (support.card : ℂ) * representation.character representative := by
      calc
        (∑ element ∈ support, representation.character element) =
            ∑ _element ∈ support, representation.character representative := by
          apply Finset.sum_congr rfl
          intro element hmember
          obtain ⟨conjugator, rfl⟩ := isConj_iff.mp (hconjugate element hmember)
          exact Representation.char_conj representation representative conjugator
        _ = (support.card : ℂ) * representation.character representative := by simp
    change (∑ element ∈ support, representation.character element) =
      scalar * representation.character 1 at hequal
    exact hequal.symm.trans hconstant
  have hscalareq : scalar = support.card * representation.character representative /
      representation.character 1 := (eq_div_iff hdegree).mpr htrace
  rw [hscalar, hscalareq]

theorem irreducible_conjugacy_class_quadratic_evaluation {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (representative : G) (support : Finset G)
    (hinvariant : ∀ conjugator element : G,
      element ∈ support ↔ conjugator * element * conjugator⁻¹ ∈ support)
    (hconjugate : ∀ element ∈ support, IsConj representative element)
    (hdegree : representation.character 1 ≠ 0) :
    ∑ left ∈ support, ∑ right ∈ support, representation.character (left * right) =
      (support.card : ℂ) ^ 2 * representation.character representative ^ 2 /
        representation.character 1 := by
  have hsum := irreducible_conjugacy_class_sum representation representative support hinvariant
    hconjugate hdegree
  have hproduct : (∑ element ∈ support, representation element) *
      (∑ element ∈ support, representation element) =
      ∑ left ∈ support, ∑ right ∈ support, representation (left * right) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro left _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right _
    rw [map_mul]
  have htrace := congrArg (LinearMap.trace ℂ vector) hproduct
  rw [hsum, smul_mul_assoc, mul_smul_comm, one_mul, map_smul, map_smul,
    LinearMap.trace_one, ← Representation.char_one representation, map_sum] at htrace
  have htrace' : (support.card * representation.character representative / representation.character 1) *
      ((support.card * representation.character representative / representation.character 1) *
        representation.character 1) =
      ∑ left ∈ support, ∑ right ∈ support, representation.character (left * right) := by
    simpa only [map_sum, smul_eq_mul, Representation.character] using htrace
  rw [← htrace']
  field_simp

end CFSG.TwoRankLowerBound.Helpers
