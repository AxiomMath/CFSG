module

public import CFSG.Combinatorics.HexagonLayersPoints

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.HexagonOppositeEdge

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dist_eq_three_of_adj_adj (H : MooreHyp G) (col : G.Coloring Bool) {t a b n : V}
    (ha : G.dist t a = 4) (hb : G.dist t b = 4) (hab : a ≠ b) (han : G.Adj a n)
    (hbn : G.Adj b n) : G.dist t n = 3 := by
  rcases dist_adj H.conn col han t with h | h
  · exact absurd (pred_unique H.cyc H.conn (k := 4) (by norm_num) (by omega) han.symm hbn.symm
      ha hb) hab
  · omega

theorem edge_data (H : MooreHyp G) (col : G.Coloring Bool)
    {w x y z₀ q₀ : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hxy : (pointGraph G col).Adj x y)
    (hN : ∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
      G.neighborFinset m = {(x : V), (y : V), (z₀ : V)})
    (hq : (pointGraph G col).Adj z₀ q₀ ∧ (pointGraph G col).dist w q₀ = 1) :
    ∃ m : V, G.neighborFinset m = {(x : V), (y : V), (z₀ : V)} ∧ G.Adj (x : V) m ∧
      G.Adj (y : V) m ∧ G.dist (w : V) z₀ = 4 ∧ G.dist (q₀ : V) x = 4 ∧
      G.dist (q₀ : V) y = 4 ∧ G.dist (q₀ : V) m = 3 := by
  have hd := point_dist_eq_iff H.conn col
  have hx6 : G.dist (w : V) x = 6 := (hd w x 3).mp hx
  have hy6 : G.dist (w : V) y = 6 := (hd w y 3).mp hy
  obtain ⟨m, ⟨hxm, hym⟩, -⟩ := exists_unique_common_line H col hxy
  have hNm := hN m hxm hym
  have hzm : G.Adj (z₀ : V) m := by
    have h : (z₀ : V) ∈ G.neighborFinset m := by rw [hNm]; simp
    exact ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm
  have hwm : G.dist (w : V) m = 4 + 1 := dist_eq_five_of_adj H col hx6 hxm
  obtain ⟨a, hma, ha⟩ := pred_exists H.conn hwm
  have hz4 : G.dist (w : V) z₀ = 4 := by
    have haN : a ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr hma
    rw [hNm] at haN
    simp only [Finset.mem_insert, Finset.mem_singleton] at haN
    rcases haN with h | h | h
    · rw [h] at ha
      omega
    · rw [h] at ha
      omega
    · rw [← h]
      exact ha
  have hzq : G.dist (z₀ : V) q₀ = 2 := (point_adj_iff H.conn col _ _).mp hq.1
  have hwq : G.dist (w : V) q₀ = 2 := (hd w _ 1).mp hq.2
  have hqx : G.dist (q₀ : V) x = 4 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_four_of_lower H hx6 hxm hzm hwq hzq
  have hqy : G.dist (q₀ : V) y = 4 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_four_of_lower H hy6 hym hzm hwq hzq
  have hqm : G.dist (q₀ : V) m = 3 := by
    have h1 : G.dist (q₀ : V) m ≤ G.dist (q₀ : V) z₀ + G.dist (z₀ : V) m :=
      H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hzm,
      SimpleGraph.dist_comm (u := (q₀ : V)) (v := (z₀ : V)), hzq] at h1
    rcases dist_adj H.conn col hxm (q₀ : V) with h | h <;> omega
  exact ⟨m, hNm, hxm, hym, hz4, hqx, hqy, hqm⟩

theorem exists_adj_colour_eq (H : MooreHyp G) (col : G.Coloring Bool)
    {w : {v : V // col v = false}} {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj (w : V) (ℓ i)) {p : Fin 3 → Fin 2 → {v : V // col v = false}}
    (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i)) (hpw : ∀ i e, p i e ≠ w)
    (hp : ∀ i, Function.Injective (p i))
    {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
    {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
    {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
    (hdata : ∀ x, (pointGraph G col).dist w x = 3 → ∀ y, (pointGraph G col).dist w y = 3 →
      (pointGraph G col).Adj x y →
      (∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
        G.neighborFinset m = {(x : V), (y : V), (z x y : V)}) ∧
      (∀ t, (pointGraph G col).Adj (z x y) t ∧ (pointGraph G col).dist w t = 1 ↔ t = q x y) ∧
      q x y = p (c x y) (ε x y))
    {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3) (i : Fin 3) :
    ∃ y, (pointGraph G col).dist w y = 3 ∧ (pointGraph G col).Adj x y ∧ c x y = i := by
  have hd := point_dist_eq_iff H.conn col
  have hA := point_adj_iff H.conn col
  have hx6 : G.dist (w : V) x = 6 := (hd w x 3).mp hx
  obtain ⟨e₀, he₀⟩ : ∃ e₀, (pointGraph G col).dist x (p i e₀) = 2 := by
    rcases bits H col hwℓ hpℓ hpw hp hx i with ⟨h0, -⟩ | ⟨-, h1⟩
    exacts [⟨0, h0⟩, ⟨1, h1⟩]
  have hq2 := dist_label H col hwℓ hpℓ hpw i e₀
  have hxq : G.dist (x : V) (p i e₀) = 4 := (hd x _ 2).mp he₀
  obtain ⟨m, y, t, hxm, hym, htm, hyx, hy, ht, htq⟩ := exists_far_edge H col hx6 hq2 hxq
  obtain ⟨y, rfl⟩ : ∃ y' : {v : V // col v = false}, (y' : V) = y :=
    ⟨⟨y, col_eq_false_of_adj col (col_eq_true_of_adj col x.2 hxm) hym⟩, rfl⟩
  have hyO : (pointGraph G col).dist w y = 3 := (hd w y 3).mpr hy
  have hxy : (pointGraph G col).Adj x y := (hA x y).mpr
    (dist_eq_two_of_adj_adj H.conn col (fun h => hyx h.symm) (x.2.trans y.2.symm) hxm hym)
  refine ⟨y, hyO, hxy, ?_⟩
  obtain ⟨hN, hq, hl⟩ := hdata x hx y hyO hxy
  have htN : t ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr htm.symm
  rw [hN m hxm hym] at htN
  simp only [Finset.mem_insert, Finset.mem_singleton] at htN
  have htz : t = (z x y : V) := by
    rcases htN with h | h | h
    · rw [h] at ht
      omega
    · rw [h] at ht
      omega
    · exact h
  have hpz := (hq (p i e₀)).mp ⟨(hA _ _).mpr (by rw [← htz]; exact htq), (hd w _ 1).mpr hq2⟩
  rw [← hpz] at hl
  exact ((label_injective H col hℓ hwℓ hpℓ hpw hp hl).1).symm

end CFSG.Combinatorics.HexagonOppositeEdge
