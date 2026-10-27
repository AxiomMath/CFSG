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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.Holt.General

open MulAction Subgroup Equiv Equiv.Perm
open scoped Pointwise

section Perfect

variable {G H : Type*} [Group G] [Group H]

theorem eq_one_of_isPerfect_of_isSolvable_range [Group.IsPerfect G] (f : G →* H)
    (hf : Group.IsSolvable f.range) : f = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := by
    by_contra hne
    rw [not_subsingleton_iff_nontrivial] at hne
    exact Group.IsPerfect.not_isSolvable f.range hf
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  exact congrArg Subtype.val (Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1)

theorem eq_one_of_isPerfect_of_isPGroup [Group.IsPerfect G] [Finite H] {p : ℕ} [Fact p.Prime]
    (hH : IsPGroup p H) (f : G →* H) : f = 1 := by
  have := (hH.to_subgroup f.range).isNilpotent
  exact eq_one_of_isPerfect_of_isSolvable_range f inferInstance

end Perfect

variable {X : Type*} [Group X]

theorem le_of_isPerfect_of_forall_pow_mem [Finite X] {N K : Subgroup X} (hN : ⁅N, N⁆ = N)
    (hNK : N ≤ normalizer (K : Set X)) {p : ℕ} [Fact p.Prime]
    (h : ∀ g ∈ N, ∃ k : ℕ, g ^ p ^ k ∈ K) : N ≤ K := by
  have : (K.subgroupOf N).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (mem_normalizer_iff.mp (hNK g.2) n).mp hn
  have : Group.IsPerfect N := isPerfect_iff.mpr hN
  have hq : IsPGroup p (N ⧸ K.subgroupOf N) := fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h g g.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow]
    exact hk
  intro g hg
  have := DFunLike.congr_fun (eq_one_of_isPerfect_of_isPGroup hq (QuotientGroup.mk' _)) ⟨g, hg⟩
  rwa [QuotientGroup.mk'_apply, MonoidHom.one_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at this

end CFSG.Holt.General
