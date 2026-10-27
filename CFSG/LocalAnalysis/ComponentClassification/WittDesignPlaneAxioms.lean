module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace CFSG.ComponentClassification.WittDesign

variable {P : Type*} [Fintype P] [DecidableEq P]

@[expose] def IsSteinerPlane (𝓛 : Finset (Finset P)) : Prop :=
  Fintype.card P = 21 ∧ (∀ L ∈ 𝓛, L.card = 5) ∧
    ∀ T : Finset P, T.card = 2 → ∃! L, L ∈ 𝓛 ∧ T ⊆ L

variable {𝓛 : Finset (Finset P)}

omit [DecidableEq P] in
theorem IsSteinerPlane.card_points (h : IsSteinerPlane 𝓛) : Fintype.card P = 21 := h.1

omit [DecidableEq P] in
theorem IsSteinerPlane.card_line (h : IsSteinerPlane 𝓛) {L : Finset P} (hL : L ∈ 𝓛) :
    L.card = 5 :=
  h.2.1 L hL

theorem IsSteinerPlane.existsUnique_line (h : IsSteinerPlane 𝓛) {p q : P} (hpq : p ≠ q) :
    ∃! L, L ∈ 𝓛 ∧ p ∈ L ∧ q ∈ L := by
  obtain ⟨L, ⟨hL, hT⟩, hu⟩ := h.2.2 {p, q} (Finset.card_pair hpq)
  refine ⟨L, ⟨hL, hT (by simp), hT (by simp)⟩, fun L' hL' => hu L' ⟨hL'.1, ?_⟩⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hL'.2.1
  · exact hL'.2.2

theorem IsSteinerPlane.eq_of_mem_of_mem (h : IsSteinerPlane 𝓛) {L L' : Finset P} (hL : L ∈ 𝓛)
    (hL' : L' ∈ 𝓛) {p q : P} (hpq : p ≠ q) (hp : p ∈ L) (hq : q ∈ L) (hp' : p ∈ L')
    (hq' : q ∈ L') : L = L' := by
  obtain ⟨M, -, hu⟩ := h.existsUnique_line hpq
  exact (hu L ⟨hL, hp, hq⟩).trans (hu L' ⟨hL', hp', hq'⟩).symm

@[expose] def linesThru (𝓛 : Finset (Finset P)) (p : P) : Finset (Finset P) :=
  𝓛.filter (p ∈ ·)

omit [Fintype P] in
theorem mem_linesThru {p : P} {L : Finset P} : L ∈ linesThru 𝓛 p ↔ L ∈ 𝓛 ∧ p ∈ L := by
  simp [linesThru]

theorem IsSteinerPlane.card_linesThru (h : IsSteinerPlane 𝓛) (p : P) :
    (linesThru 𝓛 p).card = 5 := by
  have hcover : Finset.univ.erase p = (linesThru 𝓛 p).biUnion fun L => L.erase p := by
    ext q
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion,
      mem_linesThru]
    constructor
    · intro hqp
      obtain ⟨L, ⟨hL, hp, hq⟩, -⟩ := h.existsUnique_line (Ne.symm hqp)
      exact ⟨L, ⟨hL, hp⟩, hqp, hq⟩
    · rintro ⟨L, -, hqp, -⟩
      exact hqp
  have hdisj : (linesThru 𝓛 p : Set (Finset P)).PairwiseDisjoint fun L => L.erase p := by
    intro L hL L' hL' hne
    simp only [Finset.mem_coe, mem_linesThru] at hL hL'
    refine Finset.disjoint_left.2 fun q hq hq' => hne ?_
    rw [Finset.mem_erase] at hq hq'
    exact h.eq_of_mem_of_mem hL.1 hL'.1 (Ne.symm hq.1) hL.2 hq.2 hL'.2 hq'.2
  have hcard := congrArg Finset.card hcover
  rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, h.card_points,
    Finset.card_biUnion hdisj] at hcard
  have h4 : ∀ L ∈ linesThru 𝓛 p, (L.erase p).card = 4 := by
    intro L hL
    rw [mem_linesThru] at hL
    rw [Finset.card_erase_of_mem hL.2, h.card_line hL.1]
  rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul] at hcard
  omega

theorem IsSteinerPlane.exists_mem_inter (h : IsSteinerPlane 𝓛) {L L' : Finset P} (hL : L ∈ 𝓛)
    (hL' : L' ∈ 𝓛) : ∃ x, x ∈ L ∧ x ∈ L' := by
  by_cases hsub : L ⊆ L'
  · obtain ⟨x, hx⟩ : L.Nonempty := by
      rw [← Finset.card_pos, h.card_line hL]
      norm_num
    exact ⟨x, hx, hsub hx⟩
  obtain ⟨p, hpL, hpL'⟩ := Finset.not_subset.1 hsub
  have hline : ∀ q ∈ L', ∃ M, M ∈ 𝓛 ∧ p ∈ M ∧ q ∈ M := fun q hq =>
    (h.existsUnique_line fun e : p = q => hpL' (e ▸ hq)).exists
  choose! f hf using hline
  have hinj : Set.InjOn f L' := by
    intro q hq q' hq' hqq'
    by_contra hne
    have hM : f q = L' := h.eq_of_mem_of_mem (hf q hq).1 hL' hne (hf q hq).2.2
      (hqq' ▸ (hf q' hq').2.2) hq hq'
    exact hpL' (hM ▸ (hf q hq).2.1)
  have himg : L'.image f ⊆ linesThru 𝓛 p := by
    intro M hM
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hM
    exact mem_linesThru.2 ⟨(hf q hq).1, (hf q hq).2.1⟩
  have heq : L'.image f = linesThru 𝓛 p := Finset.eq_of_subset_of_card_le himg (by
    rw [Finset.card_image_of_injOn hinj, h.card_line hL', h.card_linesThru p])
  have hLmem : L ∈ L'.image f := heq ▸ mem_linesThru.2 ⟨hL, hpL⟩
  obtain ⟨q, hq, hfq⟩ := Finset.mem_image.1 hLmem
  exact ⟨q, hfq ▸ (hf q hq).2.2, hq⟩

theorem IsSteinerPlane.card_lines (h : IsSteinerPlane 𝓛) : 𝓛.card = 21 := by
  have hcount : ∑ L ∈ 𝓛, L.card = ∑ p : P, (linesThru 𝓛 p).card := by
    simp only [Finset.card_eq_sum_ones, linesThru, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_congr rfl fun L hL => h.card_line hL,
    Finset.sum_congr rfl fun p _ => h.card_linesThru p, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, h.card_points, smul_eq_mul, smul_eq_mul] at hcount
  omega

omit [Fintype P] [DecidableEq P] in
theorem map_perm_mul' (σ τ : Equiv.Perm P) (B : Finset P) :
    B.map (σ * τ).toEmbedding = (B.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

omit [Fintype P] [DecidableEq P] in
@[expose] def blockAut (𝓛 : Finset (Finset P)) : Subgroup (Equiv.Perm P) where
  carrier := {σ | ∀ B : Finset P, B.map σ.toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛}
  mul_mem' {σ τ} hσ hτ B := by
    change B.map (σ * τ).toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛
    rw [map_perm_mul', hσ, hτ]
  one_mem' B := by
    change B.map (1 : Equiv.Perm P).toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛
    rw [show (1 : Equiv.Perm P).toEmbedding = Function.Embedding.refl P from rfl, Finset.map_refl]
  inv_mem' {σ} hσ B := by
    change B.map σ⁻¹.toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛
    rw [← hσ, ← map_perm_mul', mul_inv_cancel,
      show (1 : Equiv.Perm P).toEmbedding = Function.Embedding.refl P from rfl, Finset.map_refl]

omit [Fintype P] [DecidableEq P] in
theorem mem_blockAut {σ : Equiv.Perm P} :
    σ ∈ blockAut 𝓛 ↔ ∀ B : Finset P, B.map σ.toEmbedding ∈ 𝓛 ↔ B ∈ 𝓛 := Iff.rfl

end CFSG.ComponentClassification.WittDesign
