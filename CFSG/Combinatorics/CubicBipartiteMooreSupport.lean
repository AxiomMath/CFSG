module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Finset

namespace CFSG.Combinatorics.CubicBipartiteMoore

variable {V : Type*} {G : SimpleGraph V}

theorem eleven_le_length_of_not_mem_edges
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    [DecidableEq V] {u v : V} (h : G.Adj u v) (p : G.Walk v u) (hp : s(u, v) ∉ p.edges) :
    11 ≤ p.length := by
  have hqe : s(u, v) ∉ p.bypass.edges := fun hm => hp (p.edges_bypass_subset_edges hm)
  have hcycle : (SimpleGraph.Walk.cons h p.bypass).IsCycle :=
    (SimpleGraph.Walk.cons_isCycle_iff _ h).mpr ⟨p.bypass_isPath, hqe⟩
  have h12 := hcyc u _ hcycle
  rw [SimpleGraph.Walk.length_cons] at h12
  have := p.length_bypass_le_length
  omega

theorem even_dist_iff (hconn : G.Connected) (col : G.Coloring Bool) (u v : V) :
    Even (G.dist u v) ↔ (col u ↔ col v) := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  rw [← hp]
  exact col.even_length_iff_congr p

theorem dist_adj (hconn : G.Connected) (col : G.Coloring Bool) {x y : V} (h : G.Adj x y)
    (v : V) : G.dist v y = G.dist v x + 1 ∨ G.dist v x = G.dist v y + 1 := by
  have hc : col x ≠ col y := col.valid h
  have hx := even_dist_iff hconn col v x
  have hy := even_dist_iff hconn col v y
  rcases h.diff_dist_adj (u := v) with h1 | h1 | h1
  · exfalso
    rw [h1] at hy
    apply hc
    rcases Bool.eq_false_or_eq_true (col v) with hv | hv <;>
      rcases Bool.eq_false_or_eq_true (col x) with hx' | hx' <;>
      rcases Bool.eq_false_or_eq_true (col y) with hy' | hy' <;> simp_all
  · exact Or.inl h1
  · right
    have hpos : G.dist v x ≠ 0 := by
      intro h0
      rw [h0] at h1
      have hvx : v = x := (hconn.dist_eq_zero_iff).mp h0
      have hvy : v = y := (hconn.dist_eq_zero_iff).mp (by omega)
      exact h.ne (hvx.symm.trans hvy)
    omega

theorem dist_le_of_mem_support [DecidableEq V] {v w z : V} (p : G.Walk v w)
    (hz : z ∈ p.support) : G.dist v z ≤ p.length :=
  (SimpleGraph.dist_le (p.takeUntil z hz)).trans (p.length_takeUntil_le_length hz)

theorem pred_unique (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) [DecidableEq V] {v x y₁ y₂ : V} {k : ℕ} (hk : k + 1 ≤ 5)
    (hx : G.dist v x = k + 1) (h₁ : G.Adj x y₁) (h₂ : G.Adj x y₂) (hy₁ : G.dist v y₁ = k)
    (hy₂ : G.dist v y₂ = k) : y₁ = y₂ := by
  by_contra hne
  obtain ⟨q₁, hq₁⟩ := hconn.exists_walk_length_eq_dist v y₁
  obtain ⟨q₂, hq₂⟩ := hconn.exists_walk_length_eq_dist v y₂
  have hxq : ∀ {y : V} (q : G.Walk v y), q.length = k → x ∉ q.support := by
    intro y q hq hmem
    have := dist_le_of_mem_support q hmem
    omega
  set p : G.Walk x y₁ := SimpleGraph.Walk.cons h₂ (q₂.reverse.append q₁) with hpdef
  have hp : s(y₁, x) ∉ p.edges := by
    rw [hpdef, SimpleGraph.Walk.edges_cons, List.mem_cons, not_or]
    constructor
    · intro he
      rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h2, -⟩
      · exact h₁.ne h1.symm
      · exact hne h2
    · rw [SimpleGraph.Walk.edges_append, List.mem_append, not_or]
      constructor
      · intro he
        have hmem := SimpleGraph.Walk.snd_mem_support_of_mem_edges _ he
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hmem
        exact hxq q₂ (hq₂.trans hy₂) hmem
      · intro he
        exact hxq q₁ (hq₁.trans hy₁) (SimpleGraph.Walk.snd_mem_support_of_mem_edges _ he)
  have h11 := eleven_le_length_of_not_mem_edges hcyc h₁.symm p hp
  rw [hpdef, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse] at h11
  omega

theorem pred_exists (hconn : G.Connected) {v x : V} {k : ℕ} (hx : G.dist v x = k + 1) :
    ∃ y, G.Adj x y ∧ G.dist v y = k := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x v
  rw [SimpleGraph.dist_comm, hx] at hp
  cases p with
  | nil => simp at hp
  | @cons _ y _ h p' =>
    refine ⟨y, h, ?_⟩
    rw [SimpleGraph.Walk.length_cons] at hp
    have h1 : G.dist y v ≤ k := by
      have := SimpleGraph.dist_le p'
      omega
    have h2 : G.dist v x ≤ G.dist v y + G.dist y x := hconn.dist_triangle
    rw [SimpleGraph.dist_comm (u := y) (v := x), SimpleGraph.dist_eq_one_iff_adj.mpr h] at h2
    rw [SimpleGraph.dist_comm] at h1
    omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable abbrev layer (G : SimpleGraph V) (v : V) (k : ℕ) : Finset V :=
  univ.filter fun w => G.dist v w = k

noncomputable abbrev nbrsAt (G : SimpleGraph V) [DecidableRel G.Adj] (v x : V) (k : ℕ) :
    Finset V :=
  (G.neighborFinset x).filter fun y => G.dist v y = k

theorem card_nbrsAt_pred (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) {v x : V} {k : ℕ} (hk : k + 1 ≤ 5) (hx : G.dist v x = k + 1) :
    (nbrsAt G v x k).card = 1 := by
  obtain ⟨y, hy, hyk⟩ := pred_exists hconn hx
  rw [Finset.card_eq_one]
  refine ⟨y, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun z hz => ?_⟩⟩
  · rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨hy, hyk⟩
  · rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hz
    exact pred_unique hcyc hconn hk hx hz.1 hy hz.2 hyk

theorem card_nbrsAt_succ (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3) {v x : V}
    {k : ℕ} (hk : k + 1 ≤ 5) (hx : G.dist v x = k + 1) :
    (nbrsAt G v x (k + 2)).card = 2 := by
  have hsplit : G.neighborFinset x = nbrsAt G v x k ∪ nbrsAt G v x (k + 2) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · intro hy
      rcases dist_adj hconn col hy v with h | h
      · exact Or.inr ⟨hy, by omega⟩
      · exact Or.inl ⟨hy, by omega⟩
    · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
  have hdisj : Disjoint (nbrsAt G v x k) (nbrsAt G v x (k + 2)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [Finset.mem_filter] at hy1 hy2
    omega
  have h3 := hdeg x
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hsplit, Finset.card_union_of_disjoint hdisj,
    card_nbrsAt_pred hcyc hconn hk hx] at h3
  omega

omit [DecidableEq V] in
theorem card_nbrsAt_root (hdeg : ∀ v, G.degree v = 3) (v : V) : (nbrsAt G v v 1).card = 3 := by
  have h : nbrsAt G v v 1 = G.neighborFinset v := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, and_iff_left_iff_imp]
    exact fun hy => SimpleGraph.dist_eq_one_iff_adj.mpr hy
  rw [h, SimpleGraph.card_neighborFinset_eq_degree, hdeg]

omit [DecidableEq V] in
theorem sum_card_nbrsAt (v : V) (k : ℕ) :
    ∑ x ∈ layer G v k, (nbrsAt G v x (k + 1)).card =
      ∑ y ∈ layer G v (k + 1), (nbrsAt G v y k).card := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := G.Adj)
    (s := layer G v k) (t := layer G v (k + 1))
  calc ∑ x ∈ layer G v k, (nbrsAt G v x (k + 1)).card =
        ∑ x ∈ layer G v k, ((layer G v (k + 1)).bipartiteAbove G.Adj x).card := by
        refine Finset.sum_congr rfl fun x _ => ?_
        congr 1
        ext y
        simp [Finset.bipartiteAbove, SimpleGraph.mem_neighborFinset]
        tauto
    _ = ∑ y ∈ layer G v (k + 1), ((layer G v k).bipartiteBelow G.Adj y).card := h
    _ = ∑ y ∈ layer G v (k + 1), (nbrsAt G v y k).card := by
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        ext x
        simp [Finset.bipartiteBelow, SimpleGraph.mem_neighborFinset, G.adj_comm]
        tauto

theorem card_layers (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 126) (v : V) :
    (layer G v 0).card = 1 ∧ (layer G v 1).card = 3 ∧ (layer G v 2).card = 6 ∧
      (layer G v 3).card = 12 ∧ (layer G v 4).card = 24 ∧ (layer G v 5).card = 48 ∧
      (layer G v 6).card = 32 ∧ ∀ w, G.dist v w ≤ 6 := by
  have h0 : layer G v 0 = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hconn.dist_eq_zero_iff]
    exact eq_comm
  have h1 : (layer G v 1).card = 3 := by
    have h := sum_card_nbrsAt (G := G) v 0
    rw [h0, Finset.sum_singleton, card_nbrsAt_root hdeg v] at h
    rw [Finset.sum_congr rfl (fun y hy => card_nbrsAt_pred hcyc hconn (by norm_num)
      (Finset.mem_filter.mp hy).2), Finset.sum_const, smul_eq_mul, mul_one] at h
    exact h.symm
  have hrec : ∀ k, 1 ≤ k → k + 1 ≤ 5 → (layer G v (k + 1)).card = 2 * (layer G v k).card := by
    intro k hk1 hk5
    have h := sum_card_nbrsAt (G := G) v k
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_congr rfl (fun x hx => card_nbrsAt_succ hcyc hconn col hdeg (by omega)
      (Finset.mem_filter.mp hx).2), Finset.sum_const, smul_eq_mul] at h
    rw [Finset.sum_congr rfl (fun y hy => card_nbrsAt_pred hcyc hconn hk5
      (Finset.mem_filter.mp hy).2), Finset.sum_const, smul_eq_mul, mul_one] at h
    rw [← h]
    ring
  have h2 : (layer G v 2).card = 6 := by rw [hrec 1 le_rfl (by norm_num), h1]
  have h3 : (layer G v 3).card = 12 := by rw [hrec 2 (by norm_num) (by norm_num), h2]
  have h4 : (layer G v 4).card = 24 := by rw [hrec 3 (by norm_num) (by norm_num), h3]
  have h5 : (layer G v 5).card = 48 := by rw [hrec 4 (by norm_num) (by norm_num), h4]
  have h6ge : 32 ≤ (layer G v 6).card := by
    have h : ∑ x ∈ layer G v 5, (nbrsAt G v x 6).card =
        ∑ y ∈ layer G v 6, (nbrsAt G v y 5).card := sum_card_nbrsAt (G := G) v 5
    rw [Finset.sum_congr rfl (fun x hx => card_nbrsAt_succ hcyc hconn col hdeg (k := 4)
      (by norm_num) (Finset.mem_filter.mp hx).2), Finset.sum_const, smul_eq_mul, h5] at h
    have hle : ∑ y ∈ layer G v 6, (nbrsAt G v y 5).card ≤ ∑ _y ∈ layer G v 6, 3 := by
      refine Finset.sum_le_sum fun y _ => ?_
      rw [← hdeg y, ← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_filter_le _ _
    rw [Finset.sum_const, smul_eq_mul] at hle
    omega
  set T : Finset V := univ.filter fun w => G.dist v w ≤ 6 with hTdef
  have hT : T.card = 94 + (layer G v 6).card := by
    have hmaps : (T : Set V).MapsTo (fun w => G.dist v w) (Finset.range 7 : Finset ℕ) := by
      intro w hw
      rw [Finset.mem_coe, Finset.mem_range]
      show G.dist v w < 7
      have := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ b ∈ Finset.range 7, (T.filter fun w => G.dist v w = b) = layer G v b := by
      intro b hb
      ext w
      simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro hw
      have := Finset.mem_range.mp hb
      omega
    rw [Finset.sum_congr rfl (fun b hb => by rw [hfib b hb])]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    rw [h0, Finset.card_singleton, h1, h2, h3, h4, h5]
  have hTle : T.card ≤ 126 := hcard ▸ Finset.card_le_univ T
  have h6 : (layer G v 6).card = 32 := by omega
  refine ⟨by rw [h0, Finset.card_singleton], h1, h2, h3, h4, h5, h6, fun w => ?_⟩
  by_contra hw
  have hsub : T ⊆ univ.erase w := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨fun hxw => hw ?_, Finset.mem_univ x⟩
    rw [← hxw]
    exact (Finset.mem_filter.mp hx).2
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, hcard] at this
  omega

theorem dist_le_six (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 126) (u w : V) : G.dist u w ≤ 6 :=
  (card_layers hcyc hconn col hdeg hcard u).2.2.2.2.2.2.2 w

theorem exists_dist_six (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 126) (v : V) :
    ∃ y, G.dist v y = 6 ∧ ∀ z, G.Adj y z → G.dist v z = 5 := by
  obtain ⟨-, -, -, -, -, -, h6, -⟩ := card_layers hcyc hconn col hdeg hcard v
  obtain ⟨y, hy⟩ : (layer G v 6).Nonempty := Finset.card_pos.mp (by rw [h6]; norm_num)
  have hy6 : G.dist v y = 6 := (Finset.mem_filter.mp hy).2
  refine ⟨y, hy6, fun z hz => ?_⟩
  rcases dist_adj hconn col hz v with h | h
  · have := dist_le_six hcyc hconn col hdeg hcard v z
    omega
  · omega

theorem girth_eq_twelve (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 126) : G.girth = 12 := by
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨y, hy6, hnb⟩ := exists_dist_six hcyc hconn col hdeg hcard v
  obtain ⟨z₁, z₂, hz₁, hz₂, hne⟩ : ∃ z₁ z₂, G.Adj y z₁ ∧ G.Adj y z₂ ∧ z₁ ≠ z₂ := by
    have h3 := hdeg y
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at h3
    obtain ⟨a, b, c, hab, -, -, habc⟩ := Finset.card_eq_three.mp h3
    have ha : a ∈ G.neighborFinset y := by rw [habc]; simp
    have hb : b ∈ G.neighborFinset y := by rw [habc]; simp
    rw [SimpleGraph.mem_neighborFinset] at ha hb
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨q₁, hq₁⟩ := hconn.exists_walk_length_eq_dist v z₁
  obtain ⟨q₂, hq₂⟩ := hconn.exists_walk_length_eq_dist v z₂
  rw [hnb z₁ hz₁] at hq₁
  rw [hnb z₂ hz₂] at hq₂
  have hyq : ∀ {z : V} (q : G.Walk v z), q.length = 5 → y ∉ q.support := by
    intro z q hq hmem
    have := dist_le_of_mem_support q hmem
    omega
  set p : G.Walk z₂ y := q₂.reverse.append (q₁.concat hz₁.symm) with hpdef
  have hp : s(y, z₂) ∉ p.edges := by
    rw [hpdef, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_concat,
      List.concat_eq_append, List.mem_append, List.mem_append, List.mem_singleton, not_or, not_or]
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have hmem := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hmem
      exact hyq q₂ hq₂ hmem
    · exact hyq q₁ hq₁ (SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he)
    · rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hz₁.ne h1
      · exact hne h2.symm
  have hcycle : (SimpleGraph.Walk.cons hz₂ p.bypass).IsCycle :=
    (SimpleGraph.Walk.cons_isCycle_iff _ hz₂).mpr
      ⟨p.bypass_isPath, fun hm => hp (p.edges_bypass_subset_edges hm)⟩
  have hlen : (SimpleGraph.Walk.cons hz₂ p.bypass).length ≤ 12 := by
    have h1 := p.length_bypass_le_length
    have hpl : p.length = 11 := by
      rw [hpdef, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        SimpleGraph.Walk.length_concat, hq₁, hq₂]
    rw [SimpleGraph.Walk.length_cons]
    omega
  have hgle := hcycle.girth_le_length
  obtain ⟨a, w, hw, hgw⟩ := SimpleGraph.exists_girth_eq_length.mpr (fun h => h _ hcycle)
  have := hcyc a w hw
  omega

theorem diam_eq_six (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 126) : G.diam = 6 := by
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨y, hy6, -⟩ := exists_dist_six hcyc hconn col hdeg hcard v
  have hed : G.ediam = 6 := by
    apply le_antisymm
    · apply SimpleGraph.ediam_le_of_edist_le
      intro u w
      rw [← (hconn.preconnected u w).coe_dist_eq_edist]
      exact_mod_cast dist_le_six hcyc hconn col hdeg hcard u w
    · calc (6 : ℕ∞) = G.edist v y := by
            rw [← (hconn.preconnected v y).coe_dist_eq_edist, hy6]
            rfl
        _ ≤ G.ediam := SimpleGraph.edist_le_ediam
  rw [SimpleGraph.diam, hed]
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
theorem walk_unique (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) :
    ∀ k : ℕ, k ≤ 5 → ∀ (u w : V), G.dist u w = k → ∀ (p q : G.Walk u w),
      p.length = k → q.length = k → p = q := by
  intro k
  induction k with
  | zero =>
    intro _ u w _ p q hp hq
    cases p with
    | nil =>
      cases q with
      | nil => rfl
      | cons _ _ => simp at hq
    | cons _ _ => simp at hp
  | succ k ih =>
    intro hk u w hd p q hp hq
    cases p with
    | nil => simp at hp
    | @cons _ u₁ _ h₁ p' =>
      cases q with
      | nil => simp at hq
      | @cons _ u₂ _ h₂ q' =>
        rw [SimpleGraph.Walk.length_cons] at hp hq
        have hdist : ∀ {a : V} (ha : G.Adj u a) (r : G.Walk a w), r.length = k →
            G.dist w a = k := by
          intro a ha r hr
          have h1 : G.dist a w ≤ k := hr ▸ SimpleGraph.dist_le r
          have h2 : G.dist u w ≤ G.dist u a + G.dist a w := hconn.dist_triangle
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha] at h2
          rw [SimpleGraph.dist_comm]
          omega
        have hu : u₁ = u₂ := pred_unique hcyc hconn hk
          (by rw [SimpleGraph.dist_comm]; exact hd) h₁ h₂ (hdist h₁ p' (by omega))
          (hdist h₂ q' (by omega))
        subst hu
        rw [ih (by omega) u₁ w (by rw [SimpleGraph.dist_comm]; exact hdist h₁ p' (by omega)) p' q'
          (by omega) (by omega)]

theorem card_color_classes (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (hconn : G.Connected) (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3)
    (hcard : Fintype.card V = 126) (v : V) :
    (univ.filter fun w => col w = col v).card = 63 ∧
      (univ.filter fun w => col w ≠ col v).card = 63 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, hle⟩ := card_layers hcyc hconn col hdeg hcard v
  have hpar : ∀ w, Even (G.dist v w) ↔ col w = col v := by
    intro w
    rw [even_dist_iff hconn col v w, Bool.coe_iff_coe, eq_comm]
  have hmaps : ∀ (s : Finset V), (s : Set V).MapsTo (fun w => G.dist v w)
      (Finset.range 7 : Finset ℕ) := by
    intro s w _
    rw [Finset.mem_coe, Finset.mem_range]
    show G.dist v w < 7
    have := hle w
    omega
  constructor
  · rw [Finset.card_eq_sum_card_fiberwise (hmaps _)]
    have hfib : ∀ b ∈ Finset.range 7, ((univ.filter fun w => col w = col v).filter
        fun w => G.dist v w = b).card = if Even b then (layer G v b).card else 0 := by
      intro b _
      split_ifs with hb
      · congr 1
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        intro hw
        rw [← hpar, hw]
        exact hb
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w hw hwb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rw [← hpar, hwb] at hw
        exact hb hw
    rw [Finset.sum_congr rfl hfib]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num [h0, h2, h4, h6]
  · rw [Finset.card_eq_sum_card_fiberwise (hmaps _)]
    have hfib : ∀ b ∈ Finset.range 7, ((univ.filter fun w => col w ≠ col v).filter
        fun w => G.dist v w = b).card = if Even b then 0 else (layer G v b).card := by
      intro b _
      split_ifs with hb
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w hw hwb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rw [← hwb, hpar] at hb
        exact hw hb
      · congr 1
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        intro hw hcw
        rw [← hpar, hw] at hcw
        exact hb hcw
    rw [Finset.sum_congr rfl hfib]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num [h1, h3, h5]

abbrev pointGraph (G : SimpleGraph V) (col : G.Coloring Bool) :
    SimpleGraph {v : V // col v = false} :=
  SimpleGraph.fromRel fun p q => ∃ ℓ : V, col ℓ = true ∧ G.Adj p ℓ ∧ G.Adj q ℓ

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem dist_le_two_mul_length (hconn : G.Connected) (col : G.Coloring Bool)
    {p q : {v : V // col v = false}} (w : (pointGraph G col).Walk p q) :
    G.dist (p : V) q ≤ 2 * w.length := by
  induction w with
  | nil => simp
  | @cons a b c h w ih =>
    rw [SimpleGraph.Walk.length_cons]
    have hab : G.dist (a : V) b ≤ 2 := by
      obtain ⟨-, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).mp h
      obtain ⟨ℓ, -, ha, hb⟩ : ∃ ℓ : V, col ℓ = true ∧ G.Adj (a : V) ℓ ∧ G.Adj (b : V) ℓ := by
        rcases hr with ⟨ℓ, hℓ, ha, hb⟩ | ⟨ℓ, hℓ, hb, ha⟩
        · exact ⟨ℓ, hℓ, ha, hb⟩
        · exact ⟨ℓ, hℓ, ha, hb⟩
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons ha (SimpleGraph.Walk.cons hb.symm
        SimpleGraph.Walk.nil))
      simpa using this
    have htri : G.dist (a : V) c ≤ G.dist (a : V) b + G.dist (b : V) c := hconn.dist_triangle
    omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_walk_of_dist (hconn : G.Connected) (col : G.Coloring Bool)
    (p : {v : V // col v = false}) :
    ∀ (n : ℕ) (q : {v : V // col v = false}), G.dist (p : V) q = 2 * n →
      ∃ w : (pointGraph G col).Walk p q, w.length = n := by
  intro n
  induction n with
  | zero =>
    intro q hq
    have hpq : p = q := Subtype.ext ((hconn.dist_eq_zero_iff).mp (by simpa using hq))
    subst hpq
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
    intro q hq
    obtain ⟨ℓ, hqℓ, hℓ⟩ := pred_exists hconn (show G.dist (p : V) q = (2 * n + 1) + 1 by omega)
    obtain ⟨q', hℓq', hq'⟩ := pred_exists hconn (show G.dist (p : V) ℓ = 2 * n + 1 from hℓ)
    have hcol : ∀ w : V, Even (G.dist (p : V) w) ↔ col w = false := by
      intro w
      rw [even_dist_iff hconn col (p : V) w, Bool.coe_iff_coe, p.2, eq_comm]
    have hq'P : col q' = false := (hcol q').mp ⟨n, by omega⟩
    have hℓL : col ℓ = true := by
      have h := (hcol ℓ).not.mp (by rw [hℓ, Nat.not_even_iff_odd]; exact ⟨n, by ring⟩)
      simpa using h
    obtain ⟨w', hw'⟩ := ih ⟨q', hq'P⟩ hq'
    have hadj : (pointGraph G col).Adj ⟨q', hq'P⟩ q := by
      rw [SimpleGraph.fromRel_adj]
      refine ⟨fun h => ?_, Or.inl ⟨ℓ, hℓL, hℓq'.symm, hqℓ⟩⟩
      have h' : q' = (q : V) := congrArg Subtype.val h
      rw [h'] at hq'
      omega
    exact ⟨w'.concat hadj, by rw [SimpleGraph.Walk.length_concat, hw']⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem point_dist (hconn : G.Connected) (col : G.Coloring Bool)
    (p q : {v : V // col v = false}) :
    (pointGraph G col).dist p q = G.dist (p : V) q / 2 ∧ (pointGraph G col).Reachable p q := by
  have heven : Even (G.dist (p : V) q) := by
    rw [even_dist_iff hconn col (p : V) q, Bool.coe_iff_coe, p.2, q.2]
  obtain ⟨n, hn⟩ := heven
  obtain ⟨w, hw⟩ := exists_walk_of_dist hconn col p n q (by omega)
  have hreach : (pointGraph G col).Reachable p q := ⟨w⟩
  obtain ⟨w₀, hw₀⟩ := hreach.exists_walk_length_eq_dist
  have h1 := dist_le_two_mul_length hconn col w₀
  have h2 : (pointGraph G col).dist p q ≤ n := hw ▸ SimpleGraph.dist_le w
  refine ⟨?_, hreach⟩
  omega

end CFSG.Combinatorics.CubicBipartiteMoore
