module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbTreeDist
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Tree

variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

private theorem dist_sum_eq_one_of_mem {u v w : V} (huv : T.Adj u v) (hw : w = u ∨ w = v) :
    T.dist w u + T.dist w v = 1 := by
  have h1 : T.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.2 huv
  have h2 : T.dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.2 huv.symm
  rcases hw with rfl | rfl <;> simp only [SimpleGraph.dist_self] <;> omega

private theorem eq_of_dist_sum_eq_one (hT : T.IsTree) {u v w : V}
    (h : T.dist w u + T.dist w v = 1) : w = u ∨ w = v := by
  by_contra hne
  rw [not_or] at hne
  have h1 : T.dist w u ≠ 0 := fun h0 => hne.1 (hT.connected.dist_eq_zero_iff.1 h0)
  have h2 : T.dist w v ≠ 0 := fun h0 => hne.2 (hT.connected.dist_eq_zero_iff.1 h0)
  omega

private theorem map_mem_edgeSet {G : Type*} [Group G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v) (g : G) {e : Sym2 V}
    (he : e ∈ T.edgeSet) : Sym2.map (fun x : V => g • x) e ∈ T.edgeSet := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    exact (hadj g a b).2 ((SimpleGraph.mem_edgeSet T).1 he)

@[instance_reducible] private def edgeAct {G : Type*} [Group G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v) :
    MulAction G T.edgeSet where
  smul g e := ⟨Sym2.map (fun x : V => g • x) e.1, map_mem_edgeSet hadj g e.2⟩
  one_smul e := by
    apply Subtype.ext
    show Sym2.map (fun x : V => (1 : G) • x) e.1 = e.1
    simp
  mul_smul g h e := by
    apply Subtype.ext
    show Sym2.map (fun x : V => (g * h) • x) e.1 =
      Sym2.map (fun x : V => g • x) (Sym2.map (fun x : V => h • x) e.1)
    rw [Sym2.map_map]
    congr 1
    funext x
    exact mul_smul g h x

private theorem exists_adj_of_mem_edgeSet {e : Sym2 V} (he : e ∈ T.edgeSet) :
    ∃ u v, T.Adj u v ∧ e = s(u, v) := by
  induction e using Sym2.ind with
  | h a b => exact ⟨a, b, (SimpleGraph.mem_edgeSet T).1 he, rfl⟩

theorem orbit_subset_of_adj (hT : T.IsTree) {G : Type*} [Group G] [Finite G] [MulAction G V]
    (hG : IsPGroup 2 G) (hadj : ∀ (g : G) (u v : V), T.Adj (g • u) (g • v) ↔ T.Adj u v)
    {x y : V} (hxy : T.Adj x y) (hy : ∃ g : G, g • x = y) (g : G) : g • x = x ∨ g • x = y := by
  obtain ⟨g₀, hg₀⟩ := hy
  have hdist : ∀ (k : G) (a b : V), T.dist (k • a) (k • b) = T.dist a b := fun k a b =>
    dist_perm_eq (σ := MulAction.toPerm k) (fun c d => hadj k c d) a b
  have hcard : Nat.card V = Nat.card ↥T.edgeSet + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    exact hT.card_edgeFinset.symm
  letI : MulAction G ↥T.edgeSet := edgeAct hadj
  by_cases hV : 2 ∣ Nat.card V
  ·
    have hE : ¬ 2 ∣ Nat.card ↥T.edgeSet := by omega
    obtain ⟨⟨e, he⟩, hfix⟩ := hG.nonempty_fixed_point_of_prime_not_dvd_card ↥T.edgeSet hE
    have hinvE : ∀ k : G, Sym2.map (fun x : V => k • x) e = e := fun k =>
      congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix k)
    obtain ⟨u, v, huv, rfl⟩ := exists_adj_of_mem_edgeSet he
    have hinv : ∀ (k : G) (w : V),
        T.dist (k • w) u + T.dist (k • w) v = T.dist w u + T.dist w v := by
      intro k w
      have h1 := hdist k w u
      have h2 := hdist k w v
      have hk := hinvE k
      simp only [Sym2.map_mk, Sym2.eq_iff] at hk
      rcases hk with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h3] at h1
        rw [h4] at h2
        omega
      · rw [h3] at h1
        rw [h4] at h2
        omega
    have hsum : T.dist x u + T.dist x v = T.dist y u + T.dist y v := by
      rw [← hg₀]
      exact (hinv g₀ x).symm
    have heq := eq_of_dist_sum_eq hT huv hxy hsum
    have hδx : T.dist x u + T.dist x v = 1 := by
      rcases heq with ⟨hxu, -⟩ | ⟨hxv, -⟩
      · exact dist_sum_eq_one_of_mem huv (Or.inl hxu)
      · exact dist_sum_eq_one_of_mem huv (Or.inr hxv)
    have hmem := eq_of_dist_sum_eq_one hT ((hinv g x).trans hδx)
    rcases heq with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
    · rcases hmem with h | h
      · exact Or.inl (h.trans hxu.symm)
      · exact Or.inr (h.trans hyv.symm)
    · rcases hmem with h | h
      · exact Or.inr (h.trans hyu.symm)
      · exact Or.inl (h.trans hxv.symm)
  ·
    exfalso
    obtain ⟨c, hc⟩ := hG.nonempty_fixed_point_of_prime_not_dvd_card V hV
    have hc' : g₀ • c = c := MulAction.mem_fixedPoints.1 hc g₀
    have h1 := hdist g₀ c x
    rw [hc', hg₀] at h1
    rcases dist_adj hT hxy c with h2 | h2 <;> omega

end CFSG.AGLEmbeddingD2.Tits.GN516.Tree
