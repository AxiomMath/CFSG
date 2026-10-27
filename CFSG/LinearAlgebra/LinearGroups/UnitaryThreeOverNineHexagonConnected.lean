module

public import CFSG.Combinatorics.CubicBipartiteMooreSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.LinearGroups.UnitaryThreeOverNine

variable {V : Type*} {G : SimpleGraph V}

theorem degree_eq_ncard (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = (G.neighborSet v).ncard := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

theorem ninetyFour_le_card [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length) (hconn : G.Connected)
    (col : G.Coloring Bool) (hdeg : ∀ v, G.degree v = 3) (v : V) : 94 ≤ Fintype.card V := by
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
  set T : Finset V := univ.filter fun w => G.dist v w ≤ 5 with hTdef
  have hT : T.card = 94 := by
    have hmaps : (T : Set V).MapsTo (fun w => G.dist v w) (Finset.range 6 : Finset ℕ) := by
      intro w hw
      rw [Finset.mem_coe, Finset.mem_range]
      have := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
      show G.dist v w < 6
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ b ∈ Finset.range 6, (T.filter fun w => G.dist v w = b) = layer G v b := by
      intro b hb
      ext w
      simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro hw
      have := Finset.mem_range.mp hb
      omega
    rw [Finset.sum_congr rfl (fun b hb => by rw [hfib b hb])]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    rw [h0, Finset.card_singleton, h1, h2, h3, h4, h5]
  have := Finset.card_le_univ T
  omega

theorem ninetyFour_le_ncard_supp [Finite V]
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length) (col : G.Coloring Bool)
    (hdeg : ∀ v, (G.neighborSet v).ncard = 3) (C : G.ConnectedComponent) :
    94 ≤ C.supp.ncard := by
  classical
  have := Fintype.ofFinite C
  set H := C.toSimpleGraph with hH
  have hHcyc : ∀ (x : C) (c : H.Walk x x), c.IsCycle → 12 ≤ c.length := by
    intro x c hc
    have := hcyc _ (c.map C.toSimpleGraph_hom)
      ((SimpleGraph.Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hc)
    rwa [SimpleGraph.Walk.length_map] at this
  have hHdeg : ∀ x : C, H.degree x = 3 := by
    intro x
    rw [degree_eq_ncard, ← hdeg x.1, ← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext w
    simp only [Set.mem_image, SimpleGraph.mem_neighborSet]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hw
      exact ⟨⟨w, C.mem_supp_of_adj_mem_supp x.2 hw⟩, hw, rfl⟩
  obtain ⟨x⟩ := C.connected_toSimpleGraph.nonempty
  have h94 := ninetyFour_le_card hHcyc C.connected_toSimpleGraph
    (col.comp C.toSimpleGraph_hom) hHdeg x
  rw [← Nat.card_eq_fintype_card] at h94
  rwa [← Nat.card_coe_set_eq]

theorem connected_of_ncard_lt [Finite V] [Nonempty V]
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length) (col : G.Coloring Bool)
    (hdeg : ∀ v, (G.neighborSet v).ncard = 3) (hcard : Nat.card V < 188) : G.Connected := by
  refine { preconnected := fun u v => ?_ }
  by_contra huv
  have hne : G.connectedComponentMk u ≠ G.connectedComponentMk v := fun e =>
    huv (SimpleGraph.ConnectedComponent.exact e)
  have hu := ninetyFour_le_ncard_supp hcyc col hdeg (G.connectedComponentMk u)
  have hv := ninetyFour_le_ncard_supp hcyc col hdeg (G.connectedComponentMk v)
  have hdisj : Disjoint (G.connectedComponentMk u).supp (G.connectedComponentMk v).supp := by
    rw [Set.disjoint_left]
    intro w hwu hwv
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hwu hwv
    exact hne (hwu.symm.trans hwv)
  have hle := Set.ncard_le_ncard (Set.subset_univ
    ((G.connectedComponentMk u).supp ∪ (G.connectedComponentMk v).supp))
  rw [Set.ncard_union_eq hdisj, Set.ncard_univ] at hle
  omega

theorem edist_iso_le {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.edist (e u) (e v) ≤ G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp]
    calc H.edist (e u) (e v) ≤ (p.map e.toHom).length := SimpleGraph.edist_le _
      _ = p.length := by rw [SimpleGraph.Walk.length_map]
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

theorem edist_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.edist (e u) (e v) = G.edist u v := by
  refine le_antisymm (edist_iso_le e u v) ?_
  have h2 := edist_iso_le e.symm (e u) (e v)
  rwa [RelIso.symm_apply_apply, RelIso.symm_apply_apply] at h2

theorem dist_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.dist (e u) (e v) = G.dist u v := by
  show (H.edist (e u) (e v)).toNat = (G.edist u v).toNat
  rw [edist_iso]

theorem diam_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) : H.diam = G.diam := by
  have hed : H.ediam = G.ediam := by
    refine le_antisymm (SimpleGraph.ediam_le_of_edist_le fun u v => ?_)
      (SimpleGraph.ediam_le_of_edist_le fun u v => ?_)
    · rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, edist_iso]
      exact SimpleGraph.edist_le_ediam
    · rw [← edist_iso e]
      exact SimpleGraph.edist_le_ediam
  show H.ediam.toNat = G.ediam.toNat
  rw [hed]

end CFSG.LinearGroups.UnitaryThreeOverNine
