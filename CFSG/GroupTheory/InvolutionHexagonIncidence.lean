module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
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

public section

namespace CFSG.GroupTheory.InvolutionHexagon

variable {P L : Type*} (inc : P → L → Prop)

@[expose] def incidenceGraph : SimpleGraph (P ⊕ L) :=
  SimpleGraph.fromRel fun a b => ∃ p ℓ, a = Sum.inl p ∧ b = Sum.inr ℓ ∧ inc p ℓ

@[expose] def Collinear (p q : P) : Prop :=
  ∃ ℓ, inc p ℓ ∧ inc q ℓ

@[expose] def collinearityGraph : SimpleGraph P :=
  SimpleGraph.fromRel (Collinear inc)

structure HexagonData : Prop where
  finite_points : Finite P
  finite_lines : Finite L
  card_points : Nat.card P = 63
  ncard_points : ∀ ℓ, {p | inc p ℓ}.ncard = 3
  ncard_lines : ∀ p, {ℓ | inc p ℓ}.ncard = 3
  eq_of_inc : ∀ {p q : P} {ℓ ℓ' : L}, p ≠ q → inc p ℓ → inc q ℓ → inc p ℓ' → inc q ℓ' → ℓ = ℓ'
  exists_inc_of_triangle : ∀ {a b c : P}, a ≠ b → b ≠ c → a ≠ c → Collinear inc a b →
    Collinear inc b c → Collinear inc a c → ∃ ℓ, inc a ℓ ∧ inc b ℓ ∧ inc c ℓ
  not_square : ¬ ∃ a b c d : P, [a, b, c, d].Nodup ∧ Collinear inc a b ∧ Collinear inc b c ∧
    Collinear inc c d ∧ Collinear inc d a ∧ ¬ Collinear inc a c ∧ ¬ Collinear inc b d
  not_pentagon : ¬ ∃ a b c d e : P, [a, b, c, d, e].Nodup ∧ Collinear inc a b ∧
    Collinear inc b c ∧ Collinear inc c d ∧ Collinear inc d e ∧ Collinear inc e a ∧
    ¬ Collinear inc a c ∧ ¬ Collinear inc a d ∧ ¬ Collinear inc b d ∧ ¬ Collinear inc b e ∧
    ¬ Collinear inc c e

variable {inc}

theorem Collinear.symm {p q : P} (h : Collinear inc p q) : Collinear inc q p :=
  let ⟨ℓ, hp, hq⟩ := h
  ⟨ℓ, hq, hp⟩

theorem HexagonData.eq_of_triangle (H : HexagonData inc) {a b c : P} {ℓ ℓ' : L} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) (ha : inc a ℓ) (hb : inc b ℓ) (hb' : inc b ℓ') (hc : inc c ℓ')
    (horth : Collinear inc a c) : ℓ = ℓ' := by
  obtain ⟨ℓ₀, ha₀, hb₀, hc₀⟩ := H.exists_inc_of_triangle hab hbc hac ⟨ℓ, ha, hb⟩ ⟨ℓ', hb', hc⟩
    horth
  exact (H.eq_of_inc hab ha hb ha₀ hb₀).trans (H.eq_of_inc hbc hb₀ hc₀ hb' hc)

@[simp] theorem incidenceGraph_adj_inl_inr (p : P) (ℓ : L) :
    (incidenceGraph inc).Adj (Sum.inl p) (Sum.inr ℓ) ↔ inc p ℓ := by
  rw [incidenceGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨p', ℓ', hp, hℓ, hpℓ⟩ | ⟨p', ℓ', hp, -, -⟩⟩
    · cases hp
      cases hℓ
      exact hpℓ
    · cases hp
  · intro hpℓ
    exact ⟨Sum.inl_ne_inr, Or.inl ⟨p, ℓ, rfl, rfl, hpℓ⟩⟩

@[simp] theorem incidenceGraph_adj_inr_inl (ℓ : L) (p : P) :
    (incidenceGraph inc).Adj (Sum.inr ℓ) (Sum.inl p) ↔ inc p ℓ := by
  rw [SimpleGraph.adj_comm, incidenceGraph_adj_inl_inr]

@[simp] theorem not_incidenceGraph_adj_inl_inl (p q : P) :
    ¬ (incidenceGraph inc).Adj (Sum.inl p) (Sum.inl q) := by
  rw [incidenceGraph, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨p', ℓ', -, hℓ, -⟩ | ⟨p', ℓ', -, hℓ, -⟩⟩ <;> cases hℓ

@[simp] theorem not_incidenceGraph_adj_inr_inr (ℓ ℓ' : L) :
    ¬ (incidenceGraph inc).Adj (Sum.inr ℓ) (Sum.inr ℓ') := by
  rw [incidenceGraph, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨p', ℓ'', hp, -, -⟩ | ⟨p', ℓ'', hp, -, -⟩⟩ <;> cases hp

variable (inc) in
@[expose] def incidenceColoring : (incidenceGraph inc).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun v => v.isRight) (by
    rintro (p | ℓ) (q | ℓ') hadj
    · exact absurd hadj (not_incidenceGraph_adj_inl_inl p q)
    · exact Bool.false_ne_true
    · exact Bool.false_ne_true.symm
    · exact absurd hadj (not_incidenceGraph_adj_inr_inr ℓ ℓ'))

@[simp] theorem incidenceColoring_apply (v : P ⊕ L) : incidenceColoring inc v = v.isRight :=
  rfl

theorem neighborSet_inl (p : P) :
    (incidenceGraph inc).neighborSet (Sum.inl p) = Sum.inr '' {ℓ | inc p ℓ} := by
  ext v
  rw [SimpleGraph.mem_neighborSet, Set.mem_image]
  rcases v with q | ℓ
  · constructor
    · intro hadj
      exact absurd hadj (not_incidenceGraph_adj_inl_inl p q)
    · rintro ⟨ℓ, -, hℓ⟩
      exact absurd hℓ Sum.inr_ne_inl
  · rw [incidenceGraph_adj_inl_inr]
    constructor
    · intro hpℓ
      exact ⟨ℓ, hpℓ, rfl⟩
    · rintro ⟨ℓ', hpℓ', hℓ'⟩
      cases hℓ'
      exact hpℓ'

theorem neighborSet_inr (ℓ : L) :
    (incidenceGraph inc).neighborSet (Sum.inr ℓ) = Sum.inl '' {p | inc p ℓ} := by
  ext v
  rw [SimpleGraph.mem_neighborSet, Set.mem_image]
  rcases v with q | ℓ'
  · rw [incidenceGraph_adj_inr_inl]
    constructor
    · intro hqℓ
      exact ⟨q, hqℓ, rfl⟩
    · rintro ⟨q', hq'ℓ, hq'⟩
      cases hq'
      exact hq'ℓ
  · constructor
    · intro hadj
      exact absurd hadj (not_incidenceGraph_adj_inr_inr ℓ ℓ')
    · rintro ⟨q, -, hq⟩
      exact absurd hq Sum.inl_ne_inr

theorem HexagonData.ncard_neighborSet (H : HexagonData inc) (v : P ⊕ L) :
    ((incidenceGraph inc).neighborSet v).ncard = 3 := by
  rcases v with p | ℓ
  · rw [neighborSet_inl, Set.ncard_image_of_injective _ Sum.inr_injective, H.ncard_lines]
  · rw [neighborSet_inr, Set.ncard_image_of_injective _ Sum.inl_injective, H.ncard_points]

theorem HexagonData.card_lines (H : HexagonData inc) : Nat.card L = 63 := by
  classical
  have := H.finite_points
  have := H.finite_lines
  have := Fintype.ofFinite P
  have := Fintype.ofFinite L
  have hm : ∀ p ∈ (Finset.univ : Finset P),
      ((Finset.univ : Finset L).bipartiteAbove inc p).card = 3 := by
    intro p _
    refine Eq.trans ?_ (H.ncard_lines p)
    rw [← Set.ncard_coe_finset]
    congr 1
    ext ℓ
    simp
  have hn : ∀ ℓ ∈ (Finset.univ : Finset L),
      ((Finset.univ : Finset P).bipartiteBelow inc ℓ).card = 3 := by
    intro ℓ _
    refine Eq.trans ?_ (H.ncard_points ℓ)
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  have hdc := Finset.card_mul_eq_card_mul inc hm hn
  rw [Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, H.card_points] at hdc
  omega

theorem HexagonData.card_vertices (H : HexagonData inc) : Nat.card (P ⊕ L) = 126 := by
  have := H.finite_points
  have := H.finite_lines
  rw [Nat.card_sum, H.card_points, H.card_lines]

end CFSG.GroupTheory.InvolutionHexagon
