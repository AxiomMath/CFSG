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

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne

theorem closure_primePower_eq_top {R : Type*} [Group R] [Finite R] (hR : IsSimpleGroup R)
    (p : ℕ) (hex : ∃ x : R, x ≠ 1 ∧ ∃ a : ℕ, orderOf x = p ^ a) :
    Subgroup.closure {x : R | ∃ a : ℕ, orderOf x = p ^ a} = ⊤ := by
  set S : Set R := {x : R | ∃ a : ℕ, orderOf x = p ^ a} with hS
  have hle : Subgroup.normalClosure S ≤ Subgroup.closure S := by
    refine Subgroup.closure_mono ?_
    intro y hy
    obtain ⟨x, hxS, hxy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    obtain ⟨a, ha⟩ := hxS
    refine ⟨a, ?_⟩
    rw [← ha]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
  obtain ⟨x, hx1, hxS⟩ := hex
  have hxN : x ∈ Subgroup.normalClosure S := Subgroup.subset_normalClosure hxS
  rcases hR.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure S) with h | h
  · rw [h, Subgroup.mem_bot] at hxN
    exact absurd hxN hx1
  · exact top_unique (h ▸ hle)

theorem not_isPGroup_of_simple_nonabelian {R : Type*} [Group R] [Finite R] (hR : IsSimpleGroup R)
    (hn : ∃ x y : R, x * y ≠ y * x) (p : ℕ) [Fact p.Prime] : ¬ IsPGroup p R := by
  intro hp
  have : Nontrivial R := hR.toNontrivial
  have hc : Nontrivial (Subgroup.center R) := hp.center_nontrivial
  rcases hR.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center R)
    apply hz1
    apply Subtype.ext
    have : z ∈ (⊥ : Subgroup R) := h ▸ hz
    exact Subgroup.mem_bot.1 this
  · obtain ⟨x, y, hxy⟩ := hn
    have hx : x ∈ Subgroup.center R := h ▸ Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.1 hx y).symm

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne
