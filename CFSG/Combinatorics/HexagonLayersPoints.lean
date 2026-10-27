module

public import CFSG.Combinatorics.HexagonLayersSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.Combinatorics.HexagonLayers

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem point_dist_eq_iff (hconn : G.Connected) (col : G.Coloring Bool)
    (a b : {v : V // col v = false}) (k : ℕ) :
    (pointGraph G col).dist a b = k ↔ G.dist (a : V) b = 2 * k := by
  obtain ⟨n, hn⟩ := even_dist_of_col_eq hconn col (a.2.trans b.2.symm)
  rw [(point_dist hconn col a b).1]
  constructor <;> intro h <;> omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem point_adj_iff (hconn : G.Connected) (col : G.Coloring Bool)
    (a b : {v : V // col v = false}) :
    (pointGraph G col).Adj a b ↔ G.dist (a : V) b = 2 := by
  rw [← SimpleGraph.dist_eq_one_iff_adj, point_dist_eq_iff hconn col, mul_one]

theorem exists_unique_common_line (H : MooreHyp G) (col : G.Coloring Bool)
    {x y : {v : V // col v = false}} (hxy : (pointGraph G col).Adj x y) :
    ∃! m : V, G.Adj (x : V) m ∧ G.Adj (y : V) m := by
  have h2 : G.dist (x : V) y = 2 := (point_adj_iff H.conn col x y).mp hxy
  obtain ⟨m, hxm, hym⟩ := exists_adj_adj_of_dist_eq_two H.conn h2
  refine ⟨m, ⟨hxm, hym⟩, fun m' ⟨hxm', hym'⟩ => ?_⟩
  exact pred_unique H.cyc H.conn (k := 1) (by norm_num) h2 hym' hym
    (SimpleGraph.dist_eq_one_iff_adj.mpr hxm') (SimpleGraph.dist_eq_one_iff_adj.mpr hxm)

theorem inner_layer_lines (H : MooreHyp G) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) {r : ℕ} (hr : r = 1 ∨ r = 2) (x : {v : V // col v = false})
    (hx : (pointGraph G col).dist w x = r) :
    ∃ m : V, G.Adj (x : V) m ∧
      (∀ m' : V, G.Adj (x : V) m' →
        ((∃ y : {v : V // col v = false}, G.Adj (y : V) m' ∧
          (pointGraph G col).dist w y = r - 1) ↔ m' = m)) ∧
      (∃ a t : {v : V // col v = false}, G.neighborFinset m = {(x : V), (a : V), (t : V)} ∧
        (pointGraph G col).dist w a = r - 1 ∧ (pointGraph G col).dist w t = r ∧ t ≠ x) ∧
      ∀ m' : V, G.Adj (x : V) m' → m' ≠ m → ∃ b c : {v : V // col v = false},
        G.neighborFinset m' = {(x : V), (b : V), (c : V)} ∧ b ≠ c ∧
          (pointGraph G col).dist w b = r + 1 ∧ (pointGraph G col).dist w c = r + 1 := by
  have hd := point_dist_eq_iff H.conn col
  have hx2 : G.dist (w : V) x = 2 * r := (hd w x r).mp hx
  have hx' : G.dist (w : V) x = (2 * r - 1) + 1 := by omega
  obtain ⟨m, hxm, hm⟩ := pred_exists H.conn hx'
  have hcol : ∀ {m' : V}, G.Adj (x : V) m' → ∀ {t : V}, G.Adj t m' → col t = false :=
    fun h _ ht => col_eq_false_of_adj col (col_eq_true_of_adj col x.2 h) ht
  have hmemN : ∀ {m' t : V}, t ∈ G.neighborFinset m' → G.Adj t m' := fun ht =>
    ((SimpleGraph.mem_neighborFinset _ _ _).mp ht).symm
  have hother : ∀ {m' : V}, G.Adj (x : V) m' → m' ≠ m → G.dist (w : V) m' = 2 * r + 1 := by
    intro m' hm' hne
    rcases dist_adj H.conn col hm' (w : V) with h | h
    · omega
    · exact absurd (pred_unique H.cyc H.conn (by omega) hx' hm' hxm (by omega) hm) hne
  refine ⟨m, hxm, fun m' hm' => ⟨fun ⟨y, hym', hy⟩ => ?_, fun hmm => ?_⟩, ?_,
    fun m' hm' hne => ?_⟩
  ·
    by_contra hne
    have h1 := hother hm' hne
    have h2 : G.dist (w : V) m' ≤ G.dist (w : V) y + G.dist (y : V) m' := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hym', (hd w y (r - 1)).mp hy] at h2
    omega
  ·
    subst hmm
    obtain ⟨a, hma, ha⟩ :=
      pred_exists H.conn (show G.dist (w : V) m' = (2 * r - 2) + 1 by omega)
    exact ⟨⟨a, hcol hm' hma.symm⟩, hma.symm,
      (hd w _ _).mpr (show G.dist (w : V) a = 2 * (r - 1) by omega)⟩
  ·
    obtain ⟨a, t, hN, ha, ht, htx⟩ :=
      nbrs_of_succ H col (v := (w : V)) (k := 2 * r - 2) (by omega) (by omega) hxm (by omega)
    have ham : G.Adj a m := hmemN (by rw [hN]; simp)
    have htm : G.Adj t m := hmemN (by rw [hN]; simp)
    exact ⟨⟨a, hcol hxm ham⟩, ⟨t, hcol hxm htm⟩, hN,
      (hd w _ _).mpr (show G.dist (w : V) a = 2 * (r - 1) by omega),
      (hd w _ _).mpr (show G.dist (w : V) t = 2 * r by omega),
      fun h => htx (congrArg Subtype.val h)⟩
  ·
    obtain ⟨b, c, hN, hbc, hb, hc⟩ :=
      nbrs_of_pred H col (k := 2 * r) (by omega) (hother hm' hne) hm' hx2
    have hbm : G.Adj b m' := hmemN (by rw [hN]; simp)
    have hcm : G.Adj c m' := hmemN (by rw [hN]; simp)
    exact ⟨⟨b, hcol hm' hbm⟩, ⟨c, hcol hm' hcm⟩, hN, fun h => hbc (congrArg Subtype.val h),
      (hd w _ _).mpr (show G.dist (w : V) b = 2 * (r + 1) by omega),
      (hd w _ _).mpr (show G.dist (w : V) c = 2 * (r + 1) by omega)⟩

theorem far_lines (H : MooreHyp G) (col : G.Coloring Bool) (w : {v : V // col v = false})
    (x : {v : V // col v = false}) (hx : (pointGraph G col).dist w x = 3) (m : V)
    (hm : G.Adj (x : V) m) :
    ∃ a b : {v : V // col v = false}, G.neighborFinset m = {(x : V), (a : V), (b : V)} ∧
      (pointGraph G col).dist w a = 2 ∧ (pointGraph G col).dist w b = 3 ∧ b ≠ x := by
  have hd := point_dist_eq_iff H.conn col
  have hx' : G.dist (w : V) x = 4 + 2 := (hd w x 3).mp hx
  have hwm : G.dist (w : V) m = 4 + 1 := dist_eq_five_of_adj H col hx' hm
  obtain ⟨a, t, hN, ha, ht, htx⟩ := nbrs_of_succ H col (by norm_num) hwm hm hx'
  have hcol : ∀ {u : V}, u ∈ G.neighborFinset m → col u = false := fun hu =>
    col_eq_false_of_adj col (col_eq_true_of_adj col x.2 hm)
      ((SimpleGraph.mem_neighborFinset _ _ _).mp hu).symm
  exact ⟨⟨a, hcol (by rw [hN]; simp)⟩, ⟨t, hcol (by rw [hN]; simp)⟩, hN,
    (hd w _ 2).mpr (show G.dist (w : V) a = 2 * 2 by omega),
    (hd w _ 3).mpr (show G.dist (w : V) t = 2 * 3 by omega),
    fun h => htx (congrArg Subtype.val h)⟩

theorem third_point (H : MooreHyp G) (col : G.Coloring Bool) (w : {v : V // col v = false})
    {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hxy : (pointGraph G col).Adj x y) :
    ∃ z : {v : V // col v = false}, (∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
      G.neighborFinset m = {(x : V), (y : V), (z : V)}) ∧ (pointGraph G col).dist w z = 2 := by
  have hd := point_dist_eq_iff H.conn col
  have hx' : G.dist (w : V) x = 6 := (hd w x 3).mp hx
  have hy' : G.dist (w : V) y = 6 := (hd w y 3).mp hy
  obtain ⟨m₀, ⟨hxm₀, hym₀⟩, huniq⟩ := exists_unique_common_line H col hxy
  have hwm : G.dist (w : V) m₀ = 4 + 1 := dist_eq_five_of_adj H col hx' hxm₀
  obtain ⟨z, hm₀z, hz⟩ := pred_exists H.conn hwm
  have hxy' : (x : V) ≠ y := fun h => hxy.ne (Subtype.ext h)
  have hN : G.neighborFinset m₀ = {(x : V), (y : V), z} :=
    neighborFinset_eq H hxm₀ hym₀ hm₀z.symm hxy' (by rintro rfl; omega) (by rintro rfl; omega)
  have hzcol : col z = false :=
    col_eq_false_of_adj col (col_eq_true_of_adj col x.2 hxm₀) hm₀z.symm
  refine ⟨⟨z, hzcol⟩, fun m hxm hym => ?_, (hd w _ 2).mpr (show G.dist (w : V) z = 2 * 2 by omega)⟩
  rw [huniq m ⟨hxm, hym⟩]
  exact hN

theorem exists_unique_lower_point (H : MooreHyp G) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) {t : {v : V // col v = false}}
    (ht : (pointGraph G col).dist w t = 2) :
    ∃ s : {v : V // col v = false}, ∀ s', (pointGraph G col).Adj t s' ∧
      (pointGraph G col).dist w s' = 1 ↔ s' = s := by
  have hd := point_dist_eq_iff H.conn col
  have ht' : G.dist (w : V) t = 4 := (hd w t 2).mp ht
  obtain ⟨q, htq, hq, huniq⟩ := exists_unique_lower H col ht'
  have hqcol : col q = false := by
    have h := (even_dist_iff H.conn col (w : V) q).mp (by rw [hq]; decide)
    rw [Bool.coe_iff_coe, w.2] at h
    exact h.symm
  refine ⟨⟨q, hqcol⟩, fun s' => ⟨fun ⟨h1, h2⟩ => Subtype.ext ?_, ?_⟩⟩
  · exact huniq s' ((point_adj_iff H.conn col t s').mp h1) ((hd w s' 1).mp h2)
  · rintro rfl
    exact ⟨(point_adj_iff H.conn col t _).mpr htq, (hd w _ 1).mpr hq⟩

theorem neighborFinset_root (H : MooreHyp G) {w : V} {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj w (ℓ i)) : G.neighborFinset w = {ℓ 0, ℓ 1, ℓ 2} :=
  neighborFinset_eq H (hwℓ 0).symm (hwℓ 1).symm (hwℓ 2).symm (hℓ.ne (by decide))
    (hℓ.ne (by decide)) (hℓ.ne (by decide))

theorem neighborFinset_line (H : MooreHyp G) (col : G.Coloring Bool)
    {w : {v : V // col v = false}} {ℓ : Fin 3 → V} (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    {p : Fin 3 → Fin 2 → {v : V // col v = false}} (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i)) (i : Fin 3) :
    G.neighborFinset (ℓ i) = {(w : V), (p i 0 : V), (p i 1 : V)} :=
  neighborFinset_eq H (hwℓ i) (hpℓ i 0) (hpℓ i 1) (fun h => hpw i 0 (Subtype.ext h.symm))
    (fun h => hpw i 1 (Subtype.ext h.symm)) (fun h => absurd (hp i (Subtype.ext h)) (by decide))

omit [DecidableEq V] in
theorem dist_label (H : MooreHyp G) (col : G.Coloring Bool) {w : {v : V // col v = false}}
    {ℓ : Fin 3 → V} (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    {p : Fin 3 → Fin 2 → {v : V // col v = false}} (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (i : Fin 3) (e : Fin 2) : G.dist (w : V) (p i e) = 2 := by
  rcases dist_adj H.conn col (hpℓ i e) (w : V) with h | h
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (hwℓ i)] at h
    exact absurd (Subtype.ext ((H.conn.dist_eq_zero_iff).mp (by omega)).symm) (hpw i e)
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (hwℓ i)] at h
    omega

theorem exists_label (H : MooreHyp G) (col : G.Coloring Bool) {w : {v : V // col v = false}}
    {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    {p : Fin 3 → Fin 2 → {v : V // col v = false}} (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i)) {q : V}
    (hq : G.dist (w : V) q = 2) : ∃ i e, (p i e : V) = q := by
  obtain ⟨m, hqm, hm⟩ := pred_exists H.conn (show G.dist (w : V) q = 1 + 1 from hq)
  have hmN : m ∈ G.neighborFinset (w : V) :=
    (SimpleGraph.mem_neighborFinset _ _ _).mpr (SimpleGraph.dist_eq_one_iff_adj.mp hm)
  rw [neighborFinset_root H hℓ hwℓ] at hmN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmN
  obtain ⟨i, rfl⟩ : ∃ i, ℓ i = m := by
    rcases hmN with h | h | h
    exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩]
  have hqN : q ∈ G.neighborFinset (ℓ i) := (SimpleGraph.mem_neighborFinset _ _ _).mpr hqm.symm
  rw [neighborFinset_line H col hwℓ hpℓ hpw hp i] at hqN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqN
  rcases hqN with h | h | h
  · rw [h, SimpleGraph.dist_self] at hq
    omega
  · exact ⟨i, 0, h.symm⟩
  · exact ⟨i, 1, h.symm⟩

theorem label_injective (H : MooreHyp G) (col : G.Coloring Bool) {w : {v : V // col v = false}}
    {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    {p : Fin 3 → Fin 2 → {v : V // col v = false}} (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i)) {i j : Fin 3} {e f : Fin 2}
    (h : p i e = p j f) : i = j ∧ e = f := by
  have hij : i = j := by
    by_contra hij
    have htj : G.Adj (p i e : V) (ℓ j) := by rw [h]; exact hpℓ j f
    exact hij (hℓ (pred_unique H.cyc H.conn (k := 1) (by norm_num)
      (dist_label H col hwℓ hpℓ hpw i e) (hpℓ i e) htj
      (SimpleGraph.dist_eq_one_iff_adj.mpr (hwℓ i)) (SimpleGraph.dist_eq_one_iff_adj.mpr (hwℓ j))))
  subst hij
  exact ⟨rfl, hp i h⟩

theorem bits (H : MooreHyp G) (col : G.Coloring Bool) {w : {v : V // col v = false}}
    {ℓ : Fin 3 → V} (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    {p : Fin 3 → Fin 2 → {v : V // col v = false}} (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3) (i : Fin 3) :
    ((pointGraph G col).dist x (p i 0) = 2 ∧ (pointGraph G col).dist x (p i 1) = 3) ∨
      ((pointGraph G col).dist x (p i 0) = 3 ∧ (pointGraph G col).dist x (p i 1) = 2) := by
  have hd := point_dist_eq_iff H.conn col
  have hx' : G.dist (x : V) w = 6 := by
    rw [SimpleGraph.dist_comm]
    exact (hd w x 3).mp hx
  rcases dist_four_six H col hx' (hwℓ i) (hpℓ i 0) (hpℓ i 1)
    (fun h => absurd (hp i (Subtype.ext h)) (by decide)) (fun h => hpw i 0 (Subtype.ext h))
    (fun h => hpw i 1 (Subtype.ext h)) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨(hd x _ 2).mpr h0, (hd x _ 3).mpr h1⟩
  · exact Or.inr ⟨(hd x _ 3).mpr h0, (hd x _ 2).mpr h1⟩

end CFSG.Combinatorics.HexagonLayers
