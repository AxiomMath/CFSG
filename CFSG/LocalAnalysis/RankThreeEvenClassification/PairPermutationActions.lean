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

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

def pairPermutationAction {actor : Type u} {points : Type v} [Group actor]
    (action : actor →* Equiv.Perm points) (first second : points)
    (hpreserves : ∀ member : actor, ∀ point : points,
      action member point ∈ ({first, second} : Set points) ↔
        point ∈ ({first, second} : Set points)) :
    actor →* Equiv.Perm ({first, second} : Set points) where
  toFun member := (action member).subtypePerm (hpreserves member)
  map_one' := by
    apply Equiv.ext
    intro point
    apply Subtype.ext
    change action 1 (point : points) = (point : points)
    rw [map_one]
    rfl
  map_mul' firstMember secondMember := by
    apply Equiv.ext
    intro point
    apply Subtype.ext
    change action (firstMember * secondMember) (point : points) =
      action firstMember (action secondMember (point : points))
    rw [map_mul]
    rfl

theorem pairPermutationAction_mem_kernel_iff {actor : Type u} {points : Type v} [Group actor]
    (action : actor →* Equiv.Perm points) (first second : points)
    (hpreserves : ∀ member : actor, ∀ point : points,
      action member point ∈ ({first, second} : Set points) ↔
        point ∈ ({first, second} : Set points)) (member : actor) :
    member ∈ (pairPermutationAction action first second hpreserves).ker ↔
      action member first = first ∧ action member second = second := by
  constructor
  · intro hkernel
    have heq : pairPermutationAction action first second hpreserves member = 1 := hkernel
    constructor
    · exact congrArg (fun point : ({first, second} : Set points) => (point : points))
        (DFunLike.congr_fun heq (⟨first, Set.mem_insert _ _⟩ : ({first, second} : Set points)))
    · exact congrArg (fun point : ({first, second} : Set points) => (point : points))
        (DFunLike.congr_fun heq
          (⟨second, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩ : ({first, second} : Set points)))
  · rintro ⟨hfirst, hsecond⟩
    change pairPermutationAction action first second hpreserves member = 1
    apply Equiv.ext
    intro point
    apply Subtype.ext
    change action member (point : points) = (point : points)
    rcases Set.mem_insert_iff.mp point.property with heq | heq
    · rw [heq]
      exact hfirst
    · rw [Set.mem_singleton_iff.mp heq]
      exact hsecond

theorem pairPermutationAction_range_card_dvd_two {actor : Type u} {points : Type v} [Group actor]
    (action : actor →* Equiv.Perm points) (first second : points) (hne : first ≠ second)
    (hpreserves : ∀ member : actor, ∀ point : points,
      action member point ∈ ({first, second} : Set points) ↔
        point ∈ ({first, second} : Set points)) :
    Nat.card (pairPermutationAction action first second hpreserves).range ∣ 2 := by
  classical
  have hcard : Nat.card (Equiv.Perm ({first, second} : Set points)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hpairCard : Fintype.card ({first, second} : Set points) = 2 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact Set.ncard_pair hne
    rw [hpairCard]
    decide
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

end CFSG.RankThreeEvenClassification.Helpers
