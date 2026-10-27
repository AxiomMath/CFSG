module

public import CFSG.Combinatorics.OuterLayerExtensionLines
public import CFSG.Combinatorics.OuterLayerPredecessorsGraph

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.OuterLayer

universe u u'

theorem IsOuterLine.mono {V : Type u} {G : SimpleGraph V} {col : G.Coloring Bool}
    {w : {v : V // col v = false}} {i j : ℕ} {m : V} (h : IsOuterLine G col w i m) (hji : j ≤ i) :
    IsOuterLine G col w j m :=
  ⟨h.1, fun x hx => hji.trans (h.2 x hx)⟩

section OneFrame

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}}

omit [DecidableEq V] in
theorem dist_eq_two_mul (H : MooreHyp G) (x y : {v : V // col v = false}) :
    G.dist (x : V) y = 2 * (pointGraph G col).dist x y :=
  (point_dist_eq_iff H.conn col x y _).mp rfl

theorem samePred_iff_reachable (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    (x y : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}) :
    (∃ s : {v : V // col v = false}, (pointGraph G col).dist w s = i - 1 ∧
      (pointGraph G col).Adj x s ∧ (pointGraph G col).Adj y s) ↔
      (outerRelGraph G col w i).Reachable x y := by
  obtain ⟨e, he, -⟩ := outerRelGraph_components (w := w) H hi
  have hu : ∀ (z : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i})
      (s : {v : V // col v = false}), (pointGraph G col).dist w s = i - 1 →
      (pointGraph G col).Adj (z : {v : V // col v = false}) s →
        s = e ((outerRelGraph G col w i).connectedComponentMk z) :=
    fun z s hs hzs => (existsUnique_pred H hi z.2).unique ⟨hs, hzs⟩ ⟨(e _).2, he z⟩
  constructor
  · rintro ⟨s, hs, hxs, hys⟩
    apply SimpleGraph.ConnectedComponent.exact
    exact e.injective (Subtype.ext ((hu x s hs hxs).symm.trans (hu y s hs hys)))
  · intro h
    refine ⟨e ((outerRelGraph G col w i).connectedComponentMk x), (e _).2, he x, ?_⟩
    rw [SimpleGraph.ConnectedComponent.sound h]
    exact he y

theorem outerGraph_pred_adj_iff (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {x y : {v : V // col v = false}} (hx : i ≤ (pointGraph G col).dist w x)
    (hy : i ≤ (pointGraph G col).dist w y) :
    (outerGraph G col w (i - 1)).Adj x y ↔ (outerGraph G col w i).Adj x y ∨
      ((pointGraph G col).dist w x = i ∧ (pointGraph G col).dist w y = i ∧ x ≠ y ∧
        (∃ s : {v : V // col v = false}, (pointGraph G col).dist w s = i - 1 ∧
          (pointGraph G col).Adj x s ∧ (pointGraph G col).Adj y s) ∧
        ¬ OuterRel G col w i x y) := by
  constructor
  · intro h
    obtain ⟨hxy, m, hm, xm, ym⟩ := outerGraph_adj.mp h
    by_cases hmi : IsOuterLine G col w i m
    · exact Or.inl (outerGraph_adj.mpr ⟨hxy, m, hmi, xm, ym⟩)
    right
    obtain ⟨u, um, hu⟩ : ∃ u : {v : V // col v = false}, G.Adj (u : V) m ∧
        (pointGraph G col).dist w u < i := by
      by_contra hno
      exact hmi ⟨hm.1, fun u hu => by
        by_contra h'
        exact hno ⟨u, hu, by omega⟩⟩
    have hu' : (pointGraph G col).dist w u = i - 1 := by
      have := hm.2 u um
      omega
    have hadj : ∀ {t : {v : V // col v = false}}, i ≤ (pointGraph G col).dist w t →
        G.Adj (t : V) m → (pointGraph G col).Adj t u := fun {t} ht htm =>
      (point_adj_iff H.conn col t u).mpr (dist_eq_two_of_adj_adj H.conn col
        (fun e => by rw [Subtype.ext e] at ht; omega) (t.2.trans u.2.symm) htm um)
    have hlayer : ∀ {t : {v : V // col v = false}}, i ≤ (pointGraph G col).dist w t →
        (pointGraph G col).Adj t u → (pointGraph G col).dist w t = i := by
      intro t ht htu
      have h1 := H.conn.dist_triangle (u := (w : V)) (v := (u : V)) (w := (t : V))
      rw [dist_eq_two_mul H w u, dist_eq_two_mul H w t, SimpleGraph.dist_comm (u := (u : V)),
        (point_adj_iff H.conn col t u).mp htu] at h1
      omega
    have hxi := hlayer hx (hadj hx xm)
    have hyi := hlayer hy (hadj hy ym)
    refine ⟨hxi, hyi, hxy, ⟨u, hu', hadj hx xm, hadj hy ym⟩, fun hR => ?_⟩
    obtain ⟨s, hs, hxs, -, hl⟩ := exists_pred_of_outerRel H hi hxi hyi hxy hR
    have hsu : s = u := (existsUnique_pred H hi hxi).unique ⟨hs, hxs⟩ ⟨hu', hadj hx xm⟩
    rw [hsu] at hl
    exact hl m m xm um ym um rfl
  · rintro (h | ⟨hxi, hyi, hxy, ⟨s, hs, hxs, hys⟩, hR⟩)
    · obtain ⟨hxy, m, hm, xm, ym⟩ := outerGraph_adj.mp h
      exact outerGraph_adj.mpr ⟨hxy, m, hm.mono (Nat.sub_le i 1), xm, ym⟩
    ·
      obtain ⟨m, xm, sm, ym⟩ : ∃ m : V, G.Adj (x : V) m ∧ G.Adj (s : V) m ∧ G.Adj (y : V) m := by
        by_contra hno
        exact hR (outerRel_of_pred H hi hxi hyi hs hxs hys fun m m' h1 h2 h3 _ hmm =>
          hno ⟨m, h1, h2, by rw [hmm]; exact h3⟩)
      have hN : G.neighborFinset m = {(s : V), (x : V), (y : V)} := neighborFinset_eq H sm xm ym
        (fun e => hxs.ne (Subtype.ext e).symm) (fun e => hys.ne (Subtype.ext e).symm)
        (fun e => hxy (Subtype.ext e))
      refine outerGraph_adj.mpr ⟨hxy, m, ⟨col_eq_true_of_adj col x.2 xm, fun u hu => ?_⟩, xm, ym⟩
      have huN : (u : V) ∈ G.neighborFinset m :=
        (SimpleGraph.mem_neighborFinset _ _ _).mpr hu.symm
      rw [hN] at huN
      simp only [Finset.mem_insert, Finset.mem_singleton] at huN
      rcases huN with h | h | h
      · rw [Subtype.ext h, hs]
      · rw [Subtype.ext h, hxi]
        exact Nat.sub_le i 1
      · rw [Subtype.ext h, hyi]
        exact Nat.sub_le i 1

theorem outerGraph_pred_adj_low_iff (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {s x : {v : V // col v = false}} (hs : (pointGraph G col).dist w s = i - 1)
    (hx : i ≤ (pointGraph G col).dist w x) :
    (outerGraph G col w (i - 1)).Adj s x ↔
      (pointGraph G col).dist w x = i ∧ (pointGraph G col).Adj x s := by
  constructor
  · intro h
    obtain ⟨hsx, m, -, sm, xm⟩ := outerGraph_adj.mp h
    have hxs : (pointGraph G col).Adj x s := (point_adj_iff H.conn col x s).mpr
      (dist_eq_two_of_adj_adj H.conn col (fun e => hsx (Subtype.ext e).symm)
        (x.2.trans s.2.symm) xm sm)
    refine ⟨?_, hxs⟩
    have h1 := H.conn.dist_triangle (u := (w : V)) (v := (s : V)) (w := (x : V))
    rw [dist_eq_two_mul H w s, dist_eq_two_mul H w x, SimpleGraph.dist_comm (u := (s : V)),
      (point_adj_iff H.conn col x s).mp hxs] at h1
    omega
  · rintro ⟨hxi, hxs⟩
    obtain ⟨m₀, -, hmchar, ⟨a, t, hN, ha, ht, -⟩, -⟩ := inner_layer_lines H col w hi x hxi
    obtain ⟨m, xm, sm⟩ :=
      exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col x s).mp hxs)
    have hmm : m = m₀ := (hmchar m xm).mp ⟨s, sm, hs⟩
    rw [hmm] at sm xm
    refine outerGraph_adj.mpr ⟨hxs.ne.symm, m₀, ⟨col_eq_true_of_adj col x.2 xm, fun u hu => ?_⟩,
      sm, xm⟩
    have huN : (u : V) ∈ G.neighborFinset m₀ := (SimpleGraph.mem_neighborFinset _ _ _).mpr hu.symm
    rw [hN] at huN
    simp only [Finset.mem_insert, Finset.mem_singleton] at huN
    rcases huN with h | h | h
    · rw [Subtype.ext h, hxi]
      exact Nat.sub_le i 1
    · rw [Subtype.ext h, ha]
    · rw [Subtype.ext h, ht]
      exact Nat.sub_le i 1

theorem not_outerGraph_pred_adj_low (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {s t : {v : V // col v = false}} (hs : (pointGraph G col).dist w s = i - 1)
    (ht : (pointGraph G col).dist w t = i - 1) : ¬ (outerGraph G col w (i - 1)).Adj s t := by
  intro h
  obtain ⟨hst, m, hm, sm, tm⟩ := outerGraph_adj.mp h
  have hs2 := dist_eq_two_mul H w s
  have ht2 := dist_eq_two_mul H w t
  rcases dist_adj H.conn col sm (w : V) with h1 | h1
  ·
    exact hst (Subtype.ext (pred_unique H.cyc H.conn (v := (w : V)) (k := 2 * (i - 1)) (by omega)
      (by omega) sm.symm tm.symm (by omega) (by omega)))
  ·
    have hwm : G.Adj (w : V) m := (SimpleGraph.dist_eq_one_iff_adj (u := (w : V)) (v := m)).mp
      (by omega)
    have := hm.2 w hwm
    rw [SimpleGraph.dist_self] at this
    omega

end OneFrame

section TwoFrames

variable {V : Type u} {V' : Type u'} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'} [DecidableRel G'.Adj]
  {col : G.Coloring Bool} {col' : G'.Coloring Bool} {w : {v : V // col v = false}}
  {w' : {v : V' // col' v = false}}

theorem MarkedIncidenceSystem.Iso.samePred (H : MooreHyp G) (H' : MooreHyp G') {i : ℕ}
    (hi : i = 1 ∨ i = 2) (χ : (outerSystem G col w i).Iso (outerSystem G' col' w' i))
    {x y : (outerSystem G col w i).Pt} (hx : (pointGraph G col).dist w x.1 = i)
    (hy : (pointGraph G col).dist w y.1 = i)
    (h : ∃ s : {v : V // col v = false}, (pointGraph G col).dist w s = i - 1 ∧
      (pointGraph G col).Adj x.1 s ∧ (pointGraph G col).Adj y.1 s) :
    ∃ s' : {v : V' // col' v = false}, (pointGraph G' col').dist w' s' = i - 1 ∧
      (pointGraph G' col').Adj (χ.pts x).1 s' ∧ (pointGraph G' col').Adj (χ.pts y).1 s' := by
  let f : outerRelGraph G col w i →g outerRelGraph G' col' w' i :=
    { toFun := fun a => ⟨(χ.pts ⟨a.1, a.2.ge⟩).1, (χ.marked_iff ⟨a.1, a.2.ge⟩).mp a.2⟩
      map_rel' := fun {a b} hab => by
        rw [outerRelGraph, SimpleGraph.fromRel_adj] at hab ⊢
        obtain ⟨hne, hR⟩ := hab
        refine ⟨fun e => hne ?_, ?_⟩
        · have h0 := congrArg Subtype.val e
          have h1 : (χ.pts ⟨a.1, a.2.ge⟩).1 = (χ.pts ⟨b.1, b.2.ge⟩).1 := h0
          have h2 := χ.pts.injective (Subtype.ext h1)
          have h3 := congrArg Subtype.val h2
          exact Subtype.ext h3
        · rcases hR with hR | hR
          · exact Or.inl ((χ.outerRel_iff ⟨a.1, a.2.ge⟩ ⟨b.1, b.2.ge⟩).mpr hR)
          · exact Or.inr ((χ.outerRel_iff ⟨b.1, b.2.ge⟩ ⟨a.1, a.2.ge⟩).mpr hR) }
  have hr := ((samePred_iff_reachable H hi ⟨x.1, hx⟩ ⟨y.1, hy⟩).mp h).map f
  exact (samePred_iff_reachable H' hi (f ⟨x.1, hx⟩) (f ⟨y.1, hy⟩)).mpr hr

theorem exists_iso_pred (H : MooreHyp G) (H' : MooreHyp G') {i : ℕ} (hi : i = 1 ∨ i = 2)
    (ψ : (outerSystem G col w i).Iso (outerSystem G' col' w' i)) :
    ∃ χ : (outerSystem G col w (i - 1)).Iso (outerSystem G' col' w' (i - 1)),
      (∀ (x : (outerSystem G col w (i - 1)).Pt) (hx : i ≤ (pointGraph G col).dist w x.1),
        (χ.pts x).1 = (ψ.pts ⟨x.1, hx⟩).1) ∧
      ∀ (m : (outerSystem G col w (i - 1)).Ln) (hm : IsOuterLine G col w i m.1),
        (χ.lines m).1 = (ψ.lines ⟨m.1, hm⟩).1 := by
  have hex : ∀ x : {v : V // col v = false}, ∃ x' : {v : V' // col' v = false},
      ∀ h : i ≤ (pointGraph G col).dist w x, x' = (ψ.pts ⟨x, h⟩).1 := by
    intro x
    by_cases h : i ≤ (pointGraph G col).dist w x
    · exact ⟨(ψ.pts ⟨x, h⟩).1, fun _ => rfl⟩
    · exact ⟨w', fun h' => absurd h' h⟩
  choose ψ₀ hψ₀ using hex
  have hex' : ∀ x' : {v : V' // col' v = false}, ∃ x : {v : V // col v = false},
      ∀ h : i ≤ (pointGraph G' col').dist w' x', x = (ψ.symm.pts ⟨x', h⟩).1 := by
    intro x'
    by_cases h : i ≤ (pointGraph G' col').dist w' x'
    · exact ⟨(ψ.symm.pts ⟨x', h⟩).1, fun _ => rfl⟩
    · exact ⟨w, fun h' => absurd h' h⟩
  choose ψ₁ hψ₁ using hex'
  have hzex : ∀ s : {v : V // col v = false}, ∃ z : {v : V // col v = false},
      (pointGraph G col).dist w s = i - 1 →
        (pointGraph G col).dist w z = i ∧ (pointGraph G col).Adj z s := by
    intro s
    by_cases hs : (pointGraph G col).dist w s = i - 1
    · obtain ⟨z, -, hz, hzs, -⟩ := exists_outward_point H hi hs (s : V)
      exact ⟨z, fun _ => ⟨hz, hzs⟩⟩
    · exact ⟨s, fun h => absurd h hs⟩
  choose z hz using hzex
  have hprex : ∀ x' : {v : V' // col' v = false}, ∃ s' : {v : V' // col' v = false},
      (pointGraph G' col').dist w' x' = i →
        (pointGraph G' col').dist w' s' = i - 1 ∧ (pointGraph G' col').Adj x' s' := by
    intro x'
    by_cases hx : (pointGraph G' col').dist w' x' = i
    · obtain ⟨s', hs', -⟩ := existsUnique_pred H' hi hx
      exact ⟨s', fun _ => hs'⟩
    · exact ⟨x', fun h => absurd h hx⟩
  choose pr hpr using hprex
  have hΦex : ∀ x : {v : V // col v = false}, ∃ x' : {v : V' // col' v = false},
      (i ≤ (pointGraph G col).dist w x → x' = ψ₀ x) ∧
        (¬ i ≤ (pointGraph G col).dist w x → x' = pr (ψ₀ (z x))) := by
    intro x
    by_cases h : i ≤ (pointGraph G col).dist w x
    · exact ⟨ψ₀ x, fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨pr (ψ₀ (z x)), fun h' => absurd h' h, fun _ => rfl⟩
  choose Φ hΦ using hΦex
  have hΦhigh : ∀ x, i ≤ (pointGraph G col).dist w x → Φ x = ψ₀ x := fun x hx => (hΦ x).1 hx
  have hL : ∀ x, i ≤ (pointGraph G col).dist w x → i ≤ (pointGraph G' col').dist w' (ψ₀ x) ∧
      ((pointGraph G' col').dist w' (ψ₀ x) = i ↔ (pointGraph G col).dist w x = i) := by
    intro x h
    rw [hψ₀ x h]
    exact ⟨(ψ.pts ⟨x, h⟩).2, (ψ.marked_iff ⟨x, h⟩).symm⟩
  have hinv : ∀ x, i ≤ (pointGraph G col).dist w x → ψ₁ (ψ₀ x) = x := by
    intro x h
    have h' := (hL x h).1
    rw [hψ₁ _ h']
    have : (⟨ψ₀ x, h'⟩ : (outerSystem G' col' w' i).Pt) = ψ.pts ⟨x, h⟩ := Subtype.ext (hψ₀ x h)
    rw [this]
    have h5 := congrArg Subtype.val (MarkedIncidenceSystem.Iso.symm_pts_apply ψ ⟨x, h⟩)
    exact h5
  have hψ₁i : ∀ x', i ≤ (pointGraph G' col').dist w' x' → i ≤ (pointGraph G col).dist w (ψ₁ x') :=
    fun x' h' => by
      rw [hψ₁ x' h']
      exact (ψ.symm.pts ⟨x', h'⟩).2
  have hinv' : ∀ x', i ≤ (pointGraph G' col').dist w' x' → ψ₀ (ψ₁ x') = x' := by
    intro x' h'
    have h := hψ₁i x' h'
    rw [hψ₀ _ h]
    have : (⟨ψ₁ x', h⟩ : (outerSystem G col w i).Pt) = ψ.symm.pts ⟨x', h'⟩ :=
      Subtype.ext (hψ₁ x' h')
    rw [this]
    have h5 := congrArg Subtype.val (MarkedIncidenceSystem.Iso.pts_symm_apply ψ ⟨x', h'⟩)
    exact h5
  have hinj0 : ∀ x y, i ≤ (pointGraph G col).dist w x → i ≤ (pointGraph G col).dist w y →
      ψ₀ x = ψ₀ y → x = y := fun x y hx hy h => by
    rw [← hinv x hx, ← hinv y hy, h]
  have hA : ∀ x y, i ≤ (pointGraph G col).dist w x → i ≤ (pointGraph G col).dist w y →
      ((outerGraph G col w i).Adj x y ↔ (outerGraph G' col' w' i).Adj (ψ₀ x) (ψ₀ y)) := by
    intro x y hx hy
    rw [hψ₀ x hx, hψ₀ y hy]
    exact (ψ.outerGraph_adj_iff ⟨x, hx⟩ ⟨y, hy⟩).symm
  have hR : ∀ x y, i ≤ (pointGraph G col).dist w x → i ≤ (pointGraph G col).dist w y →
      (OuterRel G col w i x y ↔ OuterRel G' col' w' i (ψ₀ x) (ψ₀ y)) := by
    intro x y hx hy
    rw [hψ₀ x hx, hψ₀ y hy]
    exact (ψ.outerRel_iff ⟨x, hx⟩ ⟨y, hy⟩).symm
  have hSP : ∀ x y, (pointGraph G col).dist w x = i → (pointGraph G col).dist w y = i →
      ((∃ s : {v : V // col v = false}, (pointGraph G col).dist w s = i - 1 ∧
        (pointGraph G col).Adj x s ∧ (pointGraph G col).Adj y s) ↔
      (∃ s' : {v : V' // col' v = false}, (pointGraph G' col').dist w' s' = i - 1 ∧
        (pointGraph G' col').Adj (ψ₀ x) s' ∧ (pointGraph G' col').Adj (ψ₀ y) s')) := by
    intro x y hx hy
    rw [hψ₀ x hx.ge, hψ₀ y hy.ge]
    refine ⟨ψ.samePred H H' hi (x := ⟨x, hx.ge⟩) (y := ⟨y, hy.ge⟩) hx hy, fun h => ?_⟩
    obtain ⟨s, hs, hxs, hys⟩ := ψ.symm.samePred H' H hi ((ψ.marked_iff ⟨x, hx.ge⟩).mp hx)
      ((ψ.marked_iff ⟨y, hy.ge⟩).mp hy) h
    have ex0 := congrArg Subtype.val (MarkedIncidenceSystem.Iso.symm_pts_apply ψ ⟨x, hx.ge⟩)
    have ey0 := congrArg Subtype.val (MarkedIncidenceSystem.Iso.symm_pts_apply ψ ⟨y, hy.ge⟩)
    have ex : (ψ.symm.pts (ψ.pts ⟨x, hx.ge⟩)).1 = x := ex0
    have ey : (ψ.symm.pts (ψ.pts ⟨y, hy.ge⟩)).1 = y := ey0
    exact ⟨s, hs, ex ▸ hxs, ey ▸ hys⟩
  have hlow : ∀ s, (pointGraph G col).dist w s = i - 1 →
      (pointGraph G' col').dist w' (Φ s) = i - 1 ∧ ∀ x, (pointGraph G col).dist w x = i →
        ((pointGraph G col).Adj x s ↔ (pointGraph G' col').Adj (ψ₀ x) (Φ s)) := by
    intro s hs
    obtain ⟨hz1, hz2⟩ := hz s hs
    have hψz : (pointGraph G' col').dist w' (ψ₀ (z s)) = i := (hL (z s) hz1.ge).2.mpr hz1
    obtain ⟨hp1, hp2⟩ := hpr (ψ₀ (z s)) hψz
    rw [(hΦ s).2 (by omega)]
    refine ⟨hp1, fun x hx => ⟨fun hxs => ?_, fun hxs => ?_⟩⟩
    · obtain ⟨t', ht', hxt', hzt'⟩ := (hSP x (z s) hx hz1).mp ⟨s, hs, hxs, hz2⟩
      rw [← (existsUnique_pred H' hi hψz).unique ⟨ht', hzt'⟩ ⟨hp1, hp2⟩]
      exact hxt'
    · obtain ⟨t, ht, hxt, hzt⟩ := (hSP x (z s) hx hz1).mpr ⟨pr (ψ₀ (z s)), hp1, hxs, hp2⟩
      rw [← (existsUnique_pred H hi hz1).unique ⟨ht, hzt⟩ ⟨hs, hz2⟩]
      exact hxt
  have hrange : ∀ x : {v : V // col v = false}, i - 1 ≤ (pointGraph G col).dist w x →
      i - 1 ≤ (pointGraph G' col').dist w' (Φ x) := by
    intro x hx
    by_cases h : i ≤ (pointGraph G col).dist w x
    · rw [hΦhigh x h]
      exact (Nat.sub_le i 1).trans (hL x h).1
    · exact ((hlow x (by omega)).1).ge
  let φ : (outerSystem G col w (i - 1)).Pt → (outerSystem G' col' w' (i - 1)).Pt :=
    fun x => ⟨Φ x.1, hrange x.1 x.2⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hΦxy : Φ x = Φ y := congrArg Subtype.val hxy
    apply Subtype.ext
    change x = y
    by_cases h1 : i ≤ (pointGraph G col).dist w x <;> by_cases h2 : i ≤ (pointGraph G col).dist w y
    · rw [hΦhigh x h1, hΦhigh y h2] at hΦxy
      exact hinj0 x y h1 h2 hΦxy
    · exfalso
      have := (hL x h1).1
      rw [← hΦhigh x h1, hΦxy, (hlow y (by omega)).1] at this
      omega
    · exfalso
      have := (hL y h2).1
      rw [← hΦhigh y h2, ← hΦxy, (hlow x (by omega)).1] at this
      omega
    · obtain ⟨hzx1, hzx2⟩ := hz x (by omega)
      obtain ⟨hzy1, hzy2⟩ := hz y (by omega)
      have a1 := ((hlow x (by omega)).2 (z x) hzx1).mp hzx2
      have a2 := ((hlow y (by omega)).2 (z y) hzy1).mp hzy2
      rw [← hΦxy] at a2
      obtain ⟨t, ht, hxt, hyt⟩ :=
        (hSP (z x) (z y) hzx1 hzy1).mpr ⟨Φ x, (hlow x (by omega)).1, a1, a2⟩
      have e1 : t = x := (existsUnique_pred H hi hzx1).unique ⟨ht, hxt⟩ ⟨by omega, hzx2⟩
      have e2 : t = y := (existsUnique_pred H hi hzy1).unique ⟨ht, hyt⟩ ⟨by omega, hzy2⟩
      exact e1.symm.trans e2
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x', hx'⟩
    by_cases h : i ≤ (pointGraph G' col').dist w' x'
    · have h1 := hψ₁i x' h
      refine ⟨⟨ψ₁ x', (Nat.sub_le i 1).trans h1⟩, Subtype.ext ?_⟩
      change Φ (ψ₁ x') = x'
      rw [hΦhigh _ h1, hinv' x' h]
    · have hx1 : (pointGraph G' col').dist w' x' = i - 1 := by omega
      obtain ⟨z', -, hz', hz's, -⟩ := exists_outward_point H' hi hx1 (x' : V')
      have hy := hψ₁i z' hz'.ge
      have hy' : (pointGraph G col).dist w (ψ₁ z') = i := by
        have := (hL (ψ₁ z') hy).2
        rw [hinv' z' hz'.ge] at this
        exact this.mp hz'
      obtain ⟨s, ⟨hs, hys⟩, -⟩ := existsUnique_pred H hi hy'
      refine ⟨⟨s, hs.ge⟩, Subtype.ext ?_⟩
      change Φ s = x'
      have := ((hlow s hs).2 (ψ₁ z') hy').mp hys
      rw [hinv' z' hz'.ge] at this
      exact (existsUnique_pred H' hi hz').unique ⟨(hlow s hs).1, this⟩ ⟨hx1, hz's⟩
  let φe := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have mixed : ∀ a s, i ≤ (pointGraph G col).dist w a → (pointGraph G col).dist w s = i - 1 →
      ((outerGraph G' col' w' (i - 1)).Adj (Φ s) (Φ a) ↔ (outerGraph G col w (i - 1)).Adj s a) := by
    intro a s ha hs
    obtain ⟨hsl, hsl'⟩ := hlow s hs
    rw [hΦhigh a ha, outerGraph_pred_adj_low_iff H' hi hsl (hL a ha).1,
      outerGraph_pred_adj_low_iff H hi hs ha]
    constructor
    · rintro ⟨h1, h2⟩
      have ha' : (pointGraph G col).dist w a = i := (hL a ha).2.mp h1
      exact ⟨ha', (hsl' a ha').mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hL a ha).2.mpr h1, (hsl' a h1).mp h2⟩
  have hφadj : ∀ x y : (outerSystem G col w (i - 1)).Pt,
      (outerGraph G' col' w' (i - 1)).Adj (φe x).1 (φe y).1 ↔
        (outerGraph G col w (i - 1)).Adj x.1 y.1 := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    change (outerGraph G' col' w' (i - 1)).Adj (Φ x) (Φ y) ↔ (outerGraph G col w (i - 1)).Adj x y
    by_cases h1 : i ≤ (pointGraph G col).dist w x <;> by_cases h2 : i ≤ (pointGraph G col).dist w y
    · rw [hΦhigh x h1, hΦhigh y h2, outerGraph_pred_adj_iff H' hi (hL x h1).1 (hL y h2).1,
        outerGraph_pred_adj_iff H hi h1 h2, ← hA x y h1 h2]
      apply or_congr_right
      constructor
      · rintro ⟨e1, e2, e3, e4, e5⟩
        have e1' := (hL x h1).2.mp e1
        have e2' := (hL y h2).2.mp e2
        exact ⟨e1', e2', fun e => e3 (by rw [e]), (hSP x y e1' e2').mpr e4,
          fun hr => e5 ((hR x y h1 h2).mp hr)⟩
      · rintro ⟨e1, e2, e3, e4, e5⟩
        exact ⟨(hL x h1).2.mpr e1, (hL y h2).2.mpr e2, fun e => e3 (hinj0 x y h1 h2 e),
          (hSP x y e1 e2).mp e4, fun hr => e5 ((hR x y h1 h2).mpr hr)⟩
    · rw [(outerGraph G' col' w' (i - 1)).adj_comm, (outerGraph G col w (i - 1)).adj_comm]
      exact mixed x y h1 (by omega)
    · exact mixed y x h2 (by omega)
    · exact iff_of_false
        (not_outerGraph_pred_adj_low H' hi (hlow x (by omega)).1 (hlow y (by omega)).1)
        (not_outerGraph_pred_adj_low H hi (by omega) (by omega))
  have hφmk : ∀ x, x ∈ (outerSystem G col w (i - 1)).marked ↔
      φe x ∈ (outerSystem G' col' w' (i - 1)).marked := by
    rintro ⟨x, hx⟩
    change (pointGraph G col).dist w x = i - 1 ↔ (pointGraph G' col').dist w' (Φ x) = i - 1
    by_cases h : i ≤ (pointGraph G col).dist w x
    · rw [hΦhigh x h]
      have := (hL x h).1
      constructor <;> intro <;> omega
    · exact ⟨fun hx1 => (hlow x hx1).1, fun _ => by omega⟩
  obtain ⟨χ, hχ⟩ := exists_iso_of_pts H H' φe hφadj hφmk
  have hpts : ∀ (x : (outerSystem G col w (i - 1)).Pt) (hx : i ≤ (pointGraph G col).dist w x.1),
      (χ.pts x).1 = (ψ.pts ⟨x.1, hx⟩).1 := by
    intro x hx
    rw [hχ]
    change Φ x.1 = (ψ.pts ⟨x.1, hx⟩).1
    rw [hΦhigh _ hx, hψ₀ _ hx]
  refine ⟨χ, hpts, fun m hm => ?_⟩
  obtain ⟨a, b, _, hab, -, -, hN⟩ := exists_three_pts H m
  have am : G.Adj a.1.1 m.1 := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have bm : G.Adj b.1.1 m.1 := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have ha : i ≤ (pointGraph G col).dist w a.1 := hm.2 a.1 am
  have hb : i ≤ (pointGraph G col).dist w b.1 := hm.2 b.1 bm
  have h1 : G'.Adj (ψ.pts ⟨a.1, ha⟩).1.1 (χ.lines m).1 := by
    rw [← hpts a ha]
    exact (χ.inc_iff a m).mp am
  have h2 : G'.Adj (ψ.pts ⟨b.1, hb⟩).1.1 (χ.lines m).1 := by
    rw [← hpts b hb]
    exact (χ.inc_iff b m).mp bm
  have h3 := (ψ.inc_iff ⟨a.1, ha⟩ ⟨m.1, hm⟩).mp am
  have h4 := (ψ.inc_iff ⟨b.1, hb⟩ ⟨m.1, hm⟩).mp bm
  refine eq_of_adj_adj H' col' (fun e => hab ?_) ((ψ.pts _).1.2.trans (ψ.pts _).1.2.symm)
    h1 h2 h3 h4
  have := ψ.pts.injective (Subtype.ext (Subtype.ext e))
  have h5 := congrArg Subtype.val this
  exact Subtype.ext h5

end TwoFrames

end CFSG.Combinatorics.OuterLayer
