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

namespace CFSG.QuasithinUnique.Unc25K1

@[expose] def evB {M : Type*} [Monoid M] (a b : M) : List Bool → M
  | [] => 1
  | false :: w => a * evB a b w
  | true :: w => b * evB a b w

theorem evB_mem_closure {M : Type*} [Group M] (a b : M) (w : List Bool) :
    evB a b w ∈ Subgroup.closure ({a, b} : Set M) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons c w ih =>
    cases c
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) ih
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) ih

theorem map_evB {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M) (w : List Bool) :
    f (evB a b w) = evB (f a) (f b) w := by
  induction w with
  | nil => simp [evB]
  | cons c w ih => cases c <;> simp [evB, ih]

end CFSG.QuasithinUnique.Unc25K1
