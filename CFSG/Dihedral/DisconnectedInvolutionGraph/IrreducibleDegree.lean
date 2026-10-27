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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G Scalar Vector : Type*} [Group G] [Field Scalar]
variable [AddCommGroup Vector] [Module Scalar Vector]

theorem irreducible_representation_nontrivial_vector
    (representation : Representation Scalar G Vector) [representation.IsIrreducible] :
    Nontrivial Vector := by
  let := IsSimpleModule.nontrivial (MonoidAlgebra Scalar G) representation.asModule
  exact representation.asModuleEquiv.toEquiv.symm.nontrivial

theorem irreducible_character_degree_ne_zero [CharZero Scalar] [FiniteDimensional Scalar Vector]
    (representation : Representation Scalar G Vector) [representation.IsIrreducible] :
    representation.character 1 ≠ 0 := by
  let := irreducible_representation_nontrivial_vector representation
  rw [Representation.char_one]
  exact_mod_cast (Module.finrank_pos (R := Scalar) (M := Vector)).ne'

theorem irreducible_trivial_action_character_eq_one [FiniteDimensional Scalar Vector]
    (representation : Representation Scalar G Vector) [representation.IsIrreducible]
    (htrivial : ∀ element : G, representation element = 1) :
    representation.character = fun _ => 1 := by
  let := irreducible_representation_nontrivial_vector representation
  obtain ⟨vector, hvector⟩ := exists_ne (0 : Vector)
  let intertwiner : (Representation.trivial Scalar G Scalar).IntertwiningMap representation :=
    { toLinearMap := LinearMap.toSpanSingleton Scalar Vector vector
      isIntertwining' := by
        intro element
        rw [htrivial element]
        ext
        rfl }
  have hnonzero : intertwiner ≠ 0 := by
    intro hzero
    have hequal := congrArg (fun map => map (1 : Scalar)) hzero
    exact hvector (by simpa [intertwiner, LinearMap.toSpanSingleton] using hequal)
  have hsurjective := (Representation.IsIrreducible.surjective_or_eq_zero intertwiner).resolve_right hnonzero
  have hbound : Module.finrank Scalar Vector ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_surjective
      (f := intertwiner.toLinearMap) hsurjective
  have hdegree : Module.finrank Scalar Vector = 1 := by
    have hpos := Module.finrank_pos (R := Scalar) (M := Vector)
    omega
  funext element
  change LinearMap.trace Scalar Vector (representation element) = 1
  rw [htrivial element, LinearMap.trace_one, hdegree, Nat.cast_one]

theorem irreducible_nonprincipal_action_nontrivial [FiniteDimensional Scalar Vector]
    (representation : Representation Scalar G Vector) [representation.IsIrreducible]
    (hnonprincipal : representation.character ≠ fun _ => 1) :
    ∃ element : G, representation element ≠ 1 := by
  by_contra hnot
  push Not at hnot
  exact hnonprincipal (irreducible_trivial_action_character_eq_one representation hnot)

end CFSG.DisconnectedInvolutionGraph.Helpers
