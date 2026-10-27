module

public import CFSG.Combinatorics.OuterLayerIncidenceSystems
public import CFSG.Combinatorics.HexagonFourEdgePathSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath

namespace CFSG.Combinatorics.OuterLayer

section General

variable {W : Type*} {H' : SimpleGraph W}

theorem exists_adj_adj_of_edist_two {a b : W} (h : H'.edist a b = 2) :
    ∃ c, H'.Adj a c ∧ H'.Adj c b := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe (k := 2) h
  rcases p with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, p⟩⟩⟩ <;>
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hp <;> try omega
  exact ⟨_, h₁, h₂⟩

theorem exists_path_three_of_edist {a b : W} (h : H'.edist a b = 3) :
    ∃ c₁ c₂, H'.Adj a c₁ ∧ H'.Adj c₁ c₂ ∧ H'.Adj c₂ b := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe (k := 3) h
  rcases p with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | ⟨h₄, p⟩⟩⟩⟩ <;>
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hp <;> try omega
  exact ⟨_, _, h₁, h₂, h₃⟩

@[expose] def copies (ι : Type*) {X : Type*} (H : SimpleGraph X) : SimpleGraph (ι × X) where
  Adj a b := a.1 = b.1 ∧ H.Adj a.2 b.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => H.loopless.irrefl _ h.2⟩

end General

@[expose] def outerRelGraph {V : Type*} (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (i : ℕ) :
    SimpleGraph {x : {v : V // col v = false} // (pointGraph G col).dist w x = i} :=
  SimpleGraph.fromRel fun x y => OuterRel G col w i x y

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}}

theorem eq_of_mid_point (H : MooreHyp G) {a b x y : V} (hab : G.dist a b = 4)
    (hax : G.dist a x = 2) (hxb : G.dist x b = 2) (hay : G.dist a y = 2) (hyb : G.dist y b = 2) :
    x = y := by
  obtain ⟨nx, hxn, hbn⟩ := exists_adj_adj_of_dist_eq_two H.conn hxb
  obtain ⟨ny, hyn, hbn'⟩ := exists_adj_adj_of_dist_eq_two H.conn hyb
  have hdn : ∀ {t n : V}, G.dist a t = 2 → G.Adj t n → G.Adj b n → G.dist a n = 3 := by
    intro t n ht htn hbn
    have h1 := H.conn.dist_triangle (u := a) (v := t) (w := n)
    have h2 := H.conn.dist_triangle (u := a) (v := n) (w := b)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr htn] at h1
    rw [SimpleGraph.dist_comm (u := n), SimpleGraph.dist_eq_one_iff_adj.mpr hbn] at h2
    omega
  have hnn : nx = ny := pred_unique H.cyc H.conn (k := 3) (by norm_num)
    (show G.dist a b = 3 + 1 from hab) hbn hbn' (hdn hax hxn hbn) (hdn hay hyn hbn')
  subst hnn
  exact pred_unique H.cyc H.conn (k := 2) (by norm_num)
    (show G.dist a nx = 2 + 1 from hdn hax hxn hbn) hxn.symm hyn.symm hax hay

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem outerGraph_le (i : ℕ) : outerGraph G col w i ≤ pointGraph G col := by
  intro x y h
  obtain ⟨hxy, m, hm, hx, hy⟩ := outerGraph_adj.mp h
  rw [pointGraph, SimpleGraph.fromRel_adj]
  exact ⟨hxy, Or.inl ⟨m, hm.1, hx, hy⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem dist_le_outerDist (hconn : G.Connected) (i : ℕ) (x y : {v : V // col v = false}) :
    ((pointGraph G col).dist x y : ℕ∞) ≤ outerDist G col w i x y := by
  rw [(point_dist hconn col x y).2.coe_dist_eq_edist]
  exact SimpleGraph.edist_anti (outerGraph_le i)

theorem dist_six_of_outerDist_three (H : MooreHyp G) {i : ℕ} {a b : {v : V // col v = false}}
    (h : outerDist G col w i a b = 3) : G.dist (a : V) b = 6 := by
  have hV : ∀ {x y : {v : V // col v = false}}, x ≠ y → (x : V) ≠ y :=
    fun h h' => h (Subtype.ext h')
  obtain ⟨c₁, c₂, h₁, h₂, h₃⟩ := exists_path_three_of_edist h
  have hshort : ∀ {x : {v : V // col v = false}}, (outerGraph G col w i).Adj a x →
      (outerGraph G col w i).Adj x b → False := fun hax hxb => by
    have := SimpleGraph.edist_le (.cons hax (.cons hxb .nil))
    rw [show outerDist G col w i a b = (outerGraph G col w i).edist a b from rfl] at h
    rw [h] at this
    norm_num at this
  have hone : (outerGraph G col w i).Adj a b → False := fun hab => by
    have := SimpleGraph.edist_le (.cons hab .nil)
    rw [show outerDist G col w i a b = (outerGraph G col w i).edist a b from rfl] at h
    rw [h] at this
    norm_num at this
  obtain ⟨ne₁, n₁, hn₁, an₁, c₁n₁⟩ := outerGraph_adj.mp h₁
  obtain ⟨ne₂, n₂, hn₂, c₁n₂, c₂n₂⟩ := outerGraph_adj.mp h₂
  obtain ⟨ne₃, n₃, hn₃, c₂n₃, bn₃⟩ := outerGraph_adj.mp h₃
  have n12 : n₁ ≠ n₂ := by
    rintro rfl
    by_cases hac : a = c₂
    · subst hac
      exact hone h₃
    · exact hshort (outerGraph_adj.mpr ⟨hac, n₁, hn₁, an₁, c₂n₂⟩) h₃
  have n23 : n₂ ≠ n₃ := by
    rintro rfl
    by_cases hcb : c₁ = b
    · subst hcb
      exact hone h₁
    · exact hshort h₁ (outerGraph_adj.mpr ⟨hcb, n₂, hn₂, c₁n₂, bn₃⟩)
  exact (dist_of_path_six H col an₁ c₁n₁.symm c₁n₂ c₂n₂.symm c₂n₃ bn₃.symm (hV ne₁.symm)
    n12.symm (hV ne₂.symm) n23.symm (hV ne₃.symm)).2.2.2.2

theorem dist_four_on_line (H : MooreHyp G) (col : G.Coloring Bool) {y x u v L : V}
    (hN : G.neighborFinset L = {x, u, v}) (hxu : x ≠ u) (hxv : x ≠ v) (huv : u ≠ v)
    (hu : G.dist y u = 6) (hv : G.dist y v = 6) : G.dist y x = 4 := by
  have hmem : ∀ {t : V}, t ∈ ({x, u, v} : Finset V) → G.Adj t L := fun ht => by
    rw [← hN] at ht
    exact ((SimpleGraph.mem_neighborFinset _ _ _).mp ht).symm
  have hxL : G.Adj x L := hmem (show x ∈ ({x, u, v} : Finset V) by simp)
  have huL : G.Adj u L := hmem (show u ∈ ({x, u, v} : Finset V) by simp)
  have hvL : G.Adj v L := hmem (show v ∈ ({x, u, v} : Finset V) by simp)
  have hL : G.dist y L = 5 := dist_eq_five_of_adj H col hu huL
  rcases dist_adj H.conn col hxL.symm y with h | h
  · exact absurd (not_three_far_on_line H col (by omega) hu hv hxL huL hvL hxu hxv huv) id
  · omega

omit [DecidableEq V] in
theorem isOuterLine_of_adj (H : MooreHyp G) {i : ℕ} {t : {v : V // col v = false}} {m : V}
    (ht : (pointGraph G col).dist w t = i + 1) (htm : G.Adj (t : V) m) :
    IsOuterLine G col w i m := by
  have hd := point_dist_eq_iff H.conn col
  refine ⟨col_eq_true_of_adj col t.2 htm, fun x hx => ?_⟩
  have h1 := H.conn.dist_triangle (u := (w : V)) (v := (x : V)) (w := (t : V))
  have h2 := H.conn.dist_triangle (u := (x : V)) (v := m) (w := (t : V))
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hx, SimpleGraph.dist_comm (u := m),
    SimpleGraph.dist_eq_one_iff_adj.mpr htm] at h2
  have ht' := (hd w t _).mp ht
  rw [(point_dist H.conn col w x).1]
  omega

theorem exists_pred_of_outerRel (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = i)
    (hy : (pointGraph G col).dist w y = i) (hxy : x ≠ y) (hR : OuterRel G col w i x y) :
    ∃ s : {v : V // col v = false}, (pointGraph G col).dist w s = i - 1 ∧
      (pointGraph G col).Adj x s ∧ (pointGraph G col).Adj y s ∧
      ∀ m m' : V, G.Adj (x : V) m → G.Adj (s : V) m → G.Adj (y : V) m' → G.Adj (s : V) m' →
        m ≠ m' := by
  have hd := point_dist_eq_iff H.conn col
  have hA := point_adj_iff H.conn col
  obtain ⟨hD4, L, hL, xL, hLu⟩ := hR
  obtain ⟨m, xm, -, ⟨a, t, hN, ha, -, -⟩, hother⟩ := inner_layer_lines H col w hi x hx
  have ham : G.Adj (a : V) m := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have hLm : L ≠ m := fun e => by
    have := hL.2 a (e ▸ ham)
    omega
  obtain ⟨u, v, hNL, huv, hu, hv⟩ := hother L xL hLm
  have huL : G.Adj (u : V) L := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNL]; simp)).symm
  have hvL : G.Adj (v : V) L := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNL]; simp)).symm
  have hux : u ≠ x := fun e => by rw [e] at hu; omega
  have hvx : v ≠ x := fun e => by rw [e] at hv; omega
  have hyu := dist_six_of_outerDist_three H (hLu u huL hux)
  have hyv := dist_six_of_outerDist_three H (hLu v hvL hvx)
  have hyx : G.dist (y : V) x = 4 := dist_four_on_line H col hNL
    (fun e => hux (Subtype.ext e).symm) (fun e => hvx (Subtype.ext e).symm)
    (fun e => huv (Subtype.ext e)) hyu hyv
  have hxy2 : (pointGraph G col).dist x y = 2 := (hd x y 2).mpr (by
    rw [SimpleGraph.dist_comm]; exact hyx)
  obtain ⟨c, hxc, hcy⟩ := exists_adj_adj_of_edist_two (H' := pointGraph G col)
    (by rw [← (point_dist H.conn col x y).2.coe_dist_eq_edist, hxy2]; rfl)
  have hx2 : G.dist (w : V) x = 2 * i := (hd w x i).mp hx
  have hc : G.dist (w : V) c = 2 * (pointGraph G col).dist w c := by
    rw [(point_dist H.conn col w c).1]
    obtain ⟨n, hn⟩ := even_dist_of_col_eq H.conn col (w.2.trans c.2.symm)
    omega
  have hxc2 := (hA x c).mp hxc
  have hcy2 := (hA c y).mp hcy
  have hlayer : (pointGraph G col).dist w c = i - 1 ∨ (pointGraph G col).dist w c = i ∨
      (pointGraph G col).dist w c = i + 1 := by
    have h1 := H.conn.dist_triangle (u := (w : V)) (v := (x : V)) (w := (c : V))
    have h2 := H.conn.dist_triangle (u := (w : V)) (v := (c : V)) (w := (x : V))
    rw [SimpleGraph.dist_comm (u := (c : V))] at h2
    omega
  obtain ⟨nx, xnx, cnx⟩ := exists_adj_adj_of_dist_eq_two H.conn hxc2
  obtain ⟨ny, cny, yny⟩ := exists_adj_adj_of_dist_eq_two H.conn hcy2
  rcases hlayer with h | h | h
  ·
    refine ⟨c, h, hxc, hcy.symm, fun m₁ m₂ xm₁ cm₁ ym₂ cm₂ e => ?_⟩
    rw [← e] at ym₂
    have := dist_eq_two_of_adj_adj H.conn col (fun h' => hxy (Subtype.ext h'))
      (x.2.trans y.2.symm) xm₁ ym₂
    have := (hd x y 2).mp hxy2
    omega
  ·
    exfalso
    obtain ⟨mc, cmc, hmc, ⟨ac, tc, hNc, hac, -, -⟩, hotherc⟩ := inner_layer_lines H col w hi c h
    have key : ∀ {z : {v : V // col v = false}} {n : V}, (pointGraph G col).dist w z = i →
        z ≠ c → G.Adj (z : V) n → G.Adj (c : V) n → (z : V) = tc := by
      intro z n hz hzc zn cn
      by_cases hnm : n = mc
      · subst hnm
        have hzN : (z : V) ∈ G.neighborFinset n :=
          (SimpleGraph.mem_neighborFinset _ _ _).mpr zn.symm
        rw [hNc] at hzN
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
        rcases hzN with h' | h' | h'
        · exact absurd (Subtype.ext h') hzc
        · rw [Subtype.ext h'] at hz
          omega
        · exact h'
      · obtain ⟨b, b', hN', -, hb, hb'⟩ := hotherc n cn hnm
        have hzN : (z : V) ∈ G.neighborFinset n :=
          (SimpleGraph.mem_neighborFinset _ _ _).mpr zn.symm
        rw [hN'] at hzN
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
        rcases hzN with h' | h' | h'
        · exact absurd (Subtype.ext h') hzc
        · rw [Subtype.ext h'] at hz
          omega
        · rw [Subtype.ext h'] at hz
          omega
    exact hxy (Subtype.ext ((key hx hxc.ne xnx cnx).trans (key hy hcy.ne.symm yny cny).symm))
  ·
    exfalso
    have e1 : (outerGraph G col w i).Adj x c := outerGraph_adj.mpr
      ⟨hxc.ne, nx, isOuterLine_of_adj H h cnx, xnx, cnx⟩
    have e2 : (outerGraph G col w i).Adj c y := outerGraph_adj.mpr
      ⟨hcy.ne, ny, isOuterLine_of_adj H h cny, cny, yny⟩
    have := SimpleGraph.edist_le (.cons e1 (.cons e2 .nil))
    rw [show (outerGraph G col w i).edist x y = outerDist G col w i x y from rfl, hD4] at this
    norm_num at this

theorem outerRel_of_pred (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = i)
    (hy : (pointGraph G col).dist w y = i) {s : {v : V // col v = false}}
    (hs : (pointGraph G col).dist w s = i - 1) (hxs : (pointGraph G col).Adj x s)
    (hys : (pointGraph G col).Adj y s)
    (hlines : ∀ m m' : V, G.Adj (x : V) m → G.Adj (s : V) m → G.Adj (y : V) m' →
      G.Adj (s : V) m' → m ≠ m') : OuterRel G col w i x y := by
  have hd := point_dist_eq_iff H.conn col
  have hA := point_adj_iff H.conn col
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  have hreach := fun a b => (point_dist H.conn col a b).2
  obtain ⟨mx, xmx, smx⟩ := exists_adj_adj_of_dist_eq_two H.conn ((hA x s).mp hxs)
  obtain ⟨my, ymy, smy⟩ := exists_adj_adj_of_dist_eq_two H.conn ((hA y s).mp hys)
  have hmxy : mx ≠ my := hlines mx my xmx smx ymy smy
  have dxy : G.dist (x : V) y = 4 := by
    have d0 : G.dist (x : V) x = 0 := SimpleGraph.dist_self
    have d1 : G.dist (x : V) mx = 0 + 1 := SimpleGraph.dist_eq_one_iff_adj.mpr xmx
    have d2 := dist_step H col (t := 0) (by norm_num) d0 d1 xmx smx.symm (hV hxs.ne.symm)
    have d3 := dist_step H col (t := 1) (by norm_num) d1 d2 smx.symm smy hmxy.symm
    exact dist_step H col (t := 2) (by norm_num) d2 d3 smy ymy.symm (hV hys.ne)
  obtain ⟨m, xm, hmchar, -, hother⟩ := inner_layer_lines H col w hi x hx
  have hmx : mx = m := (hmchar mx xmx).mp ⟨s, smx, hs⟩
  obtain ⟨L, xL, hLm⟩ : ∃ L, G.Adj (x : V) L ∧ L ≠ m := by
    have h3 : (G.neighborFinset (x : V)).card = 3 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg]
    obtain ⟨L, hL, hLm⟩ := Finset.exists_mem_ne (by omega : 1 < (G.neighborFinset (x : V)).card) m
    exact ⟨L, (SimpleGraph.mem_neighborFinset _ _ _).mp hL, hLm⟩
  obtain ⟨u, v, hNL, huv, hu, hv⟩ := hother L xL hLm
  have hLpts : ∀ t : {v : V // col v = false}, G.Adj (t : V) L → t ≠ x →
      (pointGraph G col).dist w t = i + 1 := by
    intro t htL htx
    have htN : (t : V) ∈ G.neighborFinset L := (SimpleGraph.mem_neighborFinset _ _ _).mpr htL.symm
    rw [hNL] at htN
    simp only [Finset.mem_insert, Finset.mem_singleton] at htN
    rcases htN with h' | h' | h'
    · exact absurd (Subtype.ext h') htx
    · rw [Subtype.ext h']; exact hu
    · rw [Subtype.ext h']; exact hv
  have hLout : IsOuterLine G col w i L := isOuterLine_of_adj H hu
    ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNL]; simp)).symm
  obtain ⟨my', ymy', hmychar, -, hothery⟩ := inner_layer_lines H col w hi y hy
  have hmy : my = my' := (hmychar my ymy).mp ⟨s, smy, hs⟩
  obtain ⟨M, yM, hMm⟩ : ∃ M, G.Adj (y : V) M ∧ M ≠ my' := by
    have h3 : (G.neighborFinset (y : V)).card = 3 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg]
    obtain ⟨M, hM, hMm⟩ := Finset.exists_mem_ne (by omega : 1 < (G.neighborFinset (y : V)).card)
      my'
    exact ⟨M, (SimpleGraph.mem_neighborFinset _ _ _).mp hM, hMm⟩
  obtain ⟨b, b', hNM, hbb', hb, hb'⟩ := hothery M yM hMm
  have hMmem : ∀ {t : V}, t ∈ ({(y : V), (b : V), (b' : V)} : Finset V) → G.Adj t M :=
    fun ht => by
      rw [← hNM] at ht
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp ht).symm
  have hD3 : ∀ t : {v : V // col v = false}, G.Adj (t : V) L → t ≠ x →
      outerDist G col w i y t = 3 := by
    intro t htL htx
    have ht := hLpts t htL htx
    have d6 : G.dist (y : V) t = 6 := (dist_of_path_six H col ymy smy.symm smx xmx.symm xL
      htL.symm (hV hys.ne.symm) hmxy (hV hxs.ne) (by rw [hmx]; exact hLm) (hV htx)).2.2.2.2
    have hge : (3 : ℕ∞) ≤ outerDist G col w i y t := by
      have := dist_le_outerDist (w := w) H.conn i y t
      rw [(hd y t 3).mpr d6] at this
      exact_mod_cast this
    have hM5 : G.dist (t : V) M = 5 :=
      dist_eq_five_of_adj H col (by rw [SimpleGraph.dist_comm]; exact d6) yM
    obtain ⟨m₀, hm₀M, hm₀l, hm₀4⟩ : ∃ m₀ : {v : V // col v = false}, G.Adj (m₀ : V) M ∧
        (pointGraph G col).dist w m₀ = i + 1 ∧ G.dist (t : V) m₀ = 4 := by
      have hb6 : ¬ (G.dist (t : V) b = 6 ∧ G.dist (t : V) b' = 6) := fun ⟨h₁, h₂⟩ =>
        not_three_far_on_line H col (by rw [SimpleGraph.dist_comm]; exact d6) h₁ h₂
          (hMmem (by simp)) (hMmem (by simp)) (hMmem (by simp))
          (fun e => by rw [Subtype.ext e] at hy; omega)
          (fun e => by rw [Subtype.ext e] at hy; omega)
          (fun e => hbb' (Subtype.ext e))
      by_cases h₁ : G.dist (t : V) b = 6
      · have h₂ : G.dist (t : V) b' ≠ 6 := fun h₂ => hb6 ⟨h₁, h₂⟩
        refine ⟨b', hMmem (by simp), hb', ?_⟩
        rcases dist_adj H.conn col (hMmem (show (b' : V) ∈ ({(y : V), (b : V), (b' : V)} :
          Finset V) by simp)).symm (t : V) with h | h <;> omega
      · refine ⟨b, hMmem (by simp), hb, ?_⟩
        rcases dist_adj H.conn col (hMmem (show (b : V) ∈ ({(y : V), (b : V), (b' : V)} :
          Finset V) by simp)).symm (t : V) with h | h <;> omega
    obtain ⟨c₀, hm₀c₀, hc₀t⟩ := exists_adj_adj_of_edist_two (H' := pointGraph G col)
      (by rw [← (hreach m₀ t).coe_dist_eq_edist, (hd m₀ t 2).mpr (by
        rw [SimpleGraph.dist_comm]; exact hm₀4)]; rfl)
    obtain ⟨n₁, m₀n₁, c₀n₁⟩ := exists_adj_adj_of_dist_eq_two H.conn ((hA _ _).mp hm₀c₀)
    obtain ⟨n₂, c₀n₂, tn₂⟩ := exists_adj_adj_of_dist_eq_two H.conn ((hA _ _).mp hc₀t)
    have e1 : (outerGraph G col w i).Adj y m₀ := outerGraph_adj.mpr
      ⟨fun e => by rw [e, hm₀l] at hy; omega, M, isOuterLine_of_adj H hm₀l hm₀M, yM, hm₀M⟩
    have e2 : (outerGraph G col w i).Adj m₀ c₀ := outerGraph_adj.mpr
      ⟨hm₀c₀.ne, n₁, isOuterLine_of_adj H hm₀l m₀n₁, m₀n₁, c₀n₁⟩
    have e3 : (outerGraph G col w i).Adj c₀ t := outerGraph_adj.mpr
      ⟨hc₀t.ne, n₂, isOuterLine_of_adj H ht tn₂, c₀n₂, tn₂⟩
    have hle := SimpleGraph.edist_le (.cons e1 (.cons e2 (.cons e3 .nil)))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hle
    exact le_antisymm (by exact_mod_cast hle) hge
  have huL : G.Adj (u : V) L := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNL]; simp)).symm
  have hux : u ≠ x := fun e => by rw [e] at hu; omega
  have hxu : (outerGraph G col w i).Adj x u := outerGraph_adj.mpr ⟨hux.symm, L, hLout, xL, huL⟩
  have hle4 : outerDist G col w i x y ≤ 4 := by
    have h1 := (outerGraph G col w i).edist_triangle (u := x) (v := u) (w := y)
    have h2 : (outerGraph G col w i).edist u y = 3 :=
      SimpleGraph.edist_comm.trans (hD3 u huL hux)
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr hxu, h2] at h1
    exact h1.trans (by norm_num)
  have hge2 : (2 : ℕ∞) ≤ outerDist G col w i x y := by
    have := dist_le_outerDist (w := w) H.conn i x y
    rw [(hd x y 2).mpr dxy] at this
    exact_mod_cast this
  have hne2 : outerDist G col w i x y ≠ 2 := by
    intro h2
    obtain ⟨c, hxc, hcy⟩ := exists_adj_adj_of_edist_two h2
    have hcs : c = s := Subtype.ext (eq_of_mid_point H dxy ((hA x c).mp (outerGraph_le i hxc))
      ((hA c y).mp (outerGraph_le i hcy)) ((hA x s).mp hxs)
      (by rw [SimpleGraph.dist_comm]; exact (hA y s).mp hys))
    have := le_dist_of_outerGraph_adj hcy
    rw [hcs, hs] at this
    omega
  have hne3 : outerDist G col w i x y ≠ 3 := fun h3 => by
    have := dist_six_of_outerDist_three H h3
    omega
  have hD4 : outerDist G col w i x y = 4 := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, outerDist G col w i x y = n :=
      ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by decide) hle4) |>.imp fun _ h => h.symm
    rw [hn] at hle4 hge2 hne2 hne3 ⊢
    have h1 : n ≤ 4 := by exact_mod_cast hle4
    have h2 : 2 ≤ n := by exact_mod_cast hge2
    have h3 : n ≠ 2 := fun e => hne2 (by rw [e]; rfl)
    have h4 : n ≠ 3 := fun e => hne3 (by rw [e]; rfl)
    have : n = 4 := by omega
    rw [this]; rfl
  exact ⟨hD4, L, hLout, xL, hD3⟩

end CFSG.Combinatorics.OuterLayer
