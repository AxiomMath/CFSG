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
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Y Ω : Type*} [Group Y] [Finite Ω]

theorem four_point_odd_permutation_eq_one
    (hcard : Nat.card Ω = 4) (σ : Equiv.Perm Ω) (hodd : Odd (orderOf σ))
    (α β : Ω) (hne : α ≠ β) (hα : σ α = α) (hβ : σ β = β) : σ = 1 := by
  classical
  let := Fintype.ofFinite Ω
  have hsupport : σ.support ⊆ Finset.univ \ {α, β} := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    constructor
    · rintro rfl
      exact Equiv.Perm.mem_support.mp hx hα
    · rintro rfl
      exact Equiv.Perm.mem_support.mp hx hβ
  have hpair : ({α, β} : Finset Ω).card = 2 := by simp [hne]
  have hbound : σ.support.card ≤ 2 := by
    have hle := Finset.card_le_card hsupport
    rw [Finset.card_univ_sdiff,
      ← Nat.card_eq_fintype_card, hcard, hpair] at hle
    exact hle
  by_contra hnot
  have htwo : σ.support.card = 2 :=
    le_antisymm hbound (Equiv.Perm.two_le_card_support_of_ne_one hnot)
  have horder : orderOf σ = 2 := (Equiv.Perm.card_support_eq_two.mp htwo).orderOf
  rw [horder] at hodd
  exact hodd.not_two_dvd_nat dvd_rfl

theorem four_point_odd_pair_subgroup_fixes_every_point [MulAction Y Ω]
    (hcard : Nat.card Ω = 4) (A : Subgroup Y) (hodd : Odd (Nat.card A))
    (α β : Ω) (hne : α ≠ β)
    (hα : ∀ a ∈ A, a • α = α) (hβ : ∀ a ∈ A, a • β = β) :
    ∀ a ∈ A, ∀ γ : Ω, a • γ = γ := by
  intro a ha γ
  have horder : Odd (orderOf ((MulAction.toPermHom Y Ω) a)) :=
    hodd.of_dvd_nat ((orderOf_map_dvd (MulAction.toPermHom Y Ω) a).trans
      (A.orderOf_dvd_natCard ha))
  have heq := four_point_odd_permutation_eq_one hcard
    ((MulAction.toPermHom Y Ω) a) horder α β hne (hα a ha) (hβ a ha)
  exact congrArg (fun σ : Equiv.Perm Ω => σ γ) heq

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
