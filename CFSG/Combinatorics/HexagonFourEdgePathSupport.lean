module

public import CFSG.Combinatorics.HexagonOppositeEdge

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonOppositeEdge

namespace CFSG.Combinatorics.HexagonFourEdgePath

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev IsFrameData (G : SimpleGraph V) [DecidableRel G.Adj] (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (p : Fin 3 → Fin 2 → {v : V // col v = false})
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2) : Prop :=
  ∀ x, (pointGraph G col).dist w x = 3 → ∀ y, (pointGraph G col).dist w y = 3 →
    (pointGraph G col).Adj x y →
    (∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
      G.neighborFinset m = {(x : V), (y : V), (z x y : V)}) ∧
    (∀ t, (pointGraph G col).Adj (z x y) t ∧ (pointGraph G col).dist w t = 1 ↔ t = q x y) ∧
    q x y = p (c x y) (ε x y)

omit [Fintype V] [DecidableEq V] in
theorem nodup_five {a b c d e : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    [a, b, c, d, e].Nodup := by
  simp [hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

theorem count_eq_two_of (a : Fin 6 → Fin 3) (b : Fin 6 → Fin 2) (h1 : ∀ n, a n ≠ a (n + 1))
    (h2 : ∀ n, a n = a (n + 2) → b n ≠ b (n + 2)) (i : Fin 3) :
    (univ.filter fun n => a n = i).card = 2 := by
  have h6 : ∀ n : Fin 6, n + 2 + 2 + 2 = n := by decide
  have h3 : ∀ n, ¬ (a n = a (n + 2) ∧ a (n + 2) = a (n + 2 + 2)) := by
    rintro n ⟨e1, e2⟩
    have e3 : a (n + 2 + 2) = a (n + 2 + 2 + 2) := by
      rw [h6]
      exact (e1.trans e2).symm
    have b1 := h2 n e1
    have b2 := h2 (n + 2) e2
    have b3 := h2 (n + 2 + 2) e3
    rw [h6] at b3
    have key : ∀ x y t : Fin 2, x ≠ y → y ≠ t → t ≠ x → False := by decide
    exact key _ _ _ b1 b2 b3
  have key : ∀ a₀ a₁ a₂ a₃ a₄ a₅ i : Fin 3, a₀ ≠ a₁ → a₁ ≠ a₂ → a₂ ≠ a₃ → a₃ ≠ a₄ →
      a₄ ≠ a₅ → a₅ ≠ a₀ → ¬(a₀ = a₂ ∧ a₂ = a₄) → ¬(a₁ = a₃ ∧ a₃ = a₅) →
      (if a₀ = i then 1 else 0) + (if a₁ = i then 1 else 0) + (if a₂ = i then 1 else 0) +
        (if a₃ = i then 1 else 0) + (if a₄ = i then 1 else 0) + (if a₅ = i then 1 else 0) = 2 := by
    decide
  rw [Finset.card_filter, Fin.sum_univ_six]
  exact key _ _ _ _ _ _ i (h1 0) (h1 1) (h1 2) (h1 3) (h1 4) (h1 5) (h3 0) (h3 1)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dist_step (H : MooreHyp G) (col : G.Coloring Bool) {r y x x' : V} {t : ℕ}
    (ht : t + 1 ≤ 5) (hy : G.dist r y = t) (hx : G.dist r x = t + 1) (hyx : G.Adj y x)
    (hxx' : G.Adj x x') (hne : x' ≠ y) : G.dist r x' = t + 2 := by
  rcases dist_adj H.conn col hxx' r with h | h
  · omega
  · exact absurd (pred_unique H.cyc H.conn ht hx hxx' hyx.symm (by omega) hy) hne

theorem dist_of_path_six (H : MooreHyp G) (col : G.Coloring Bool) {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : V}
    (h₁ : G.Adj x₀ x₁) (h₂ : G.Adj x₁ x₂) (h₃ : G.Adj x₂ x₃) (h₄ : G.Adj x₃ x₄)
    (h₅ : G.Adj x₄ x₅) (h₆ : G.Adj x₅ x₆) (n₂ : x₂ ≠ x₀) (n₃ : x₃ ≠ x₁) (n₄ : x₄ ≠ x₂)
    (n₅ : x₅ ≠ x₃) (n₆ : x₆ ≠ x₄) :
    G.dist x₀ x₂ = 2 ∧ G.dist x₀ x₃ = 3 ∧ G.dist x₀ x₄ = 4 ∧ G.dist x₀ x₅ = 5 ∧
      G.dist x₀ x₆ = 6 := by
  have d0 : G.dist x₀ x₀ = 0 := SimpleGraph.dist_self
  have d1 : G.dist x₀ x₁ = 0 + 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h₁
  have d2 := dist_step H col (t := 0) (by norm_num) d0 d1 h₁ h₂ n₂
  have d3 := dist_step H col (t := 1) (by norm_num) d1 d2 h₂ h₃ n₃
  have d4 := dist_step H col (t := 2) (by norm_num) d2 d3 h₃ h₄ n₄
  have d5 := dist_step H col (t := 3) (by norm_num) d3 d4 h₄ h₅ n₅
  have d6 := dist_step H col (t := 4) (by norm_num) d4 d5 h₅ h₆ n₆
  exact ⟨d2, d3, d4, d5, d6⟩

theorem frame_edge (H : MooreHyp G) (col : G.Coloring Bool) {w : {v : V // col v = false}}
    {p : Fin 3 → Fin 2 → {v : V // col v = false}}
    {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
    {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
    {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
    (hdata : IsFrameData G col w p z q c ε) {x y : {v : V // col v = false}}
    (hx : (pointGraph G col).dist w x = 3) (hy : (pointGraph G col).dist w y = 3)
    (hxy : (pointGraph G col).Adj x y) :
    ∃ m : V, G.neighborFinset m = {(x : V), (y : V), (z x y : V)} ∧ G.Adj (x : V) m ∧
      G.Adj (y : V) m ∧ G.Adj (z x y : V) m ∧ G.dist (w : V) (z x y) = 4 ∧
      G.dist (w : V) (q x y) = 2 ∧ G.dist (z x y : V) (q x y) = 2 ∧
      G.dist (q x y : V) x = 4 ∧ G.dist (q x y : V) y = 4 ∧ G.dist (q x y : V) m = 3 := by
  obtain ⟨hN, hq, -⟩ := hdata x hx y hy hxy
  have hq' := (hq (q x y)).mpr rfl
  obtain ⟨m, hNm, hxm, hym, hz4, hqx, hqy, hqm⟩ := edge_data H col hx hy hxy hN hq'
  have hzm : G.Adj (z x y : V) m := by
    have h : (z x y : V) ∈ G.neighborFinset m := by rw [hNm]; simp
    exact ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm
  exact ⟨m, hNm, hxm, hym, hzm, hz4, (point_dist_eq_iff H.conn col w _ 1).mp hq'.2,
    (point_adj_iff H.conn col _ _).mp hq'.1, hqx, hqy, hqm⟩

theorem frame_symm (H : MooreHyp G) (col : G.Coloring Bool) {w : {v : V // col v = false}}
    {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    {p : Fin 3 → Fin 2 → {v : V // col v = false}} (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
    {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
    {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
    (hdata : IsFrameData G col w p z q c ε) {x y : {v : V // col v = false}}
    (hx : (pointGraph G col).dist w x = 3) (hy : (pointGraph G col).dist w y = 3)
    (hxy : (pointGraph G col).Adj x y) :
    z y x = z x y ∧ q y x = q x y ∧ c y x = c x y ∧ ε y x = ε x y := by
  obtain ⟨m, hN, hxm, hym, -, -, -, -, -, -, -⟩ := frame_edge H col hdata hx hy hxy
  obtain ⟨m', -, -, -, -, hz4', -⟩ := frame_edge H col hdata hy hx hxy.symm
  have hx6 : G.dist (w : V) x = 6 := (point_dist_eq_iff H.conn col w x 3).mp hx
  have hy6 : G.dist (w : V) y = 6 := (point_dist_eq_iff H.conn col w y 3).mp hy
  have hzyx : (z y x : V) ∈ G.neighborFinset m := by
    rw [(hdata y hy x hx hxy.symm).1 m hym hxm]; simp
  rw [hN] at hzyx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzyx
  have hz : z y x = z x y := by
    rcases hzyx with h | h | h
    · rw [h] at hz4'
      omega
    · rw [h] at hz4'
      omega
    · exact Subtype.ext h
  have hq : q y x = q x y := by
    have h1 := ((hdata x hx y hy hxy).2.1 (q x y)).mpr rfl
    rw [← hz] at h1
    exact (((hdata y hy x hx hxy.symm).2.1 (q x y)).mp h1).symm
  have hl := (hdata y hy x hx hxy.symm).2.2
  rw [hq, (hdata x hx y hy hxy).2.2] at hl
  obtain ⟨h1, h2⟩ := label_injective H col hℓ hwℓ hpℓ hpw hp hl
  exact ⟨hz, hq, h1.symm, h2.symm⟩

theorem frame_colour_unique (H : MooreHyp G) (col : G.Coloring Bool)
    {w : {v : V // col v = false}} {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj (w : V) (ℓ i)) {p : Fin 3 → Fin 2 → {v : V // col v = false}}
    (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i)) (hpw : ∀ i e, p i e ≠ w)
    (hp : ∀ i, Function.Injective (p i))
    {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
    {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
    {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
    (hdata : IsFrameData G col w p z q c ε) {x y y' : {v : V // col v = false}}
    (hx : (pointGraph G col).dist w x = 3) (hy : (pointGraph G col).dist w y = 3)
    (hy' : (pointGraph G col).dist w y' = 3) (hxy : (pointGraph G col).Adj x y)
    (hxy' : (pointGraph G col).Adj x y') (hc : c x y = c x y') : y = y' := by
  obtain ⟨-, -, -, -, -, -, -, -, hqx, -, -⟩ := frame_edge H col hdata hx hy hxy
  obtain ⟨-, -, -, -, -, -, -, -, hqx', -, -⟩ := frame_edge H col hdata hx hy' hxy'
  have hl := (hdata x hx y hy hxy).2.2
  have hl' := (hdata x hx y' hy' hxy').2.2
  rw [← hc] at hl'
  have hd2 : ∀ e : Fin 2, G.dist (p (c x y) e : V) x = 4 →
      (pointGraph G col).dist x (p (c x y) e) = 2 := fun e he =>
    (point_dist_eq_iff H.conn col x _ 2).mpr (by rw [SimpleGraph.dist_comm]; exact he)
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Fin 2, ∀ e, (pointGraph G col).dist x (p (c x y) e) = 2 ↔ e = e₀ := by
    rcases bits H col hwℓ hpℓ hpw hp hx (c x y) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨0, fun e => by fin_cases e <;> simp [h0, h1]⟩
    · exact ⟨1, fun e => by fin_cases e <;> simp [h0, h1]⟩
  have h1 : G.dist (p (c x y) (ε x y) : V) x = 4 := by rw [← hl]; exact hqx
  have h2 : G.dist (p (c x y) (ε x y') : V) x = 4 := by rw [← hl']; exact hqx'
  have hqq : q x y = q x y' := by
    rw [hl, hl', (he₀ _).mp (hd2 _ h1), (he₀ _).mp (hd2 _ h2)]
  by_contra hne
  have hsep := (opposite_edge_equal_label_separation_and_four_path_repeat G H col w ℓ hℓ hwℓ p
    hpℓ hpw hp z q c ε hdata).1 x hx y hy x hx y' hy' hxy hxy' ?_ hqq
  · exact Finset.disjoint_left.mp hsep.1
      (show x ∈ ({x, y} : Finset {v : V // col v = false}) by simp) (by simp)
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨-, h'⟩ | ⟨h', -⟩
    · exact hne h'
    · exact hxy'.ne h'

theorem six_cycle_colours (H : MooreHyp G) (col : G.Coloring Bool)
    {w : {v : V // col v = false}} {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj (w : V) (ℓ i)) {p : Fin 3 → Fin 2 → {v : V // col v = false}}
    (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i)) (hpw : ∀ i e, p i e ≠ w)
    (hp : ∀ i, Function.Injective (p i))
    {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
    {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
    {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
    (hdata : IsFrameData G col w p z q c ε) {v : Fin 6 → {v : V // col v = false}}
    (hv : Function.Injective v) (hO : ∀ n, (pointGraph G col).dist w (v n) = 3)
    (hadj : ∀ n, (pointGraph G col).Adj (v n) (v (n + 1))) (i : Fin 3) :
    (univ.filter fun n => c (v n) (v (n + 1)) = i).card = 2 := by
  obtain ⟨hsep, -⟩ := opposite_edge_equal_label_separation_and_four_path_repeat G H col w ℓ hℓ
    hwℓ p hpℓ hpw hp z q c ε hdata
  have e2 : ∀ n : Fin 6, n + 1 + 1 = n + 2 := by decide
  have n2 : ∀ n : Fin 6, n ≠ n + 2 := by decide
  have n3 : ∀ n : Fin 6, n ≠ n + 2 + 1 := by decide
  have hF1 : ∀ n, c (v n) (v (n + 1)) ≠ c (v (n + 1)) (v (n + 1 + 1)) := by
    intro n h
    rw [← (frame_symm H col hℓ hwℓ hpℓ hpw hp hdata (hO n) (hO (n + 1)) (hadj n)).2.2.1] at h
    have h' := frame_colour_unique H col hℓ hwℓ hpℓ hpw hp hdata (hO (n + 1)) (hO n)
      (hO (n + 1 + 1)) (hadj n).symm (hadj (n + 1)) h
    rw [e2] at h'
    exact n2 n (hv h')
  have hF2 : ∀ n, c (v n) (v (n + 1)) = c (v (n + 2)) (v (n + 2 + 1)) →
      ε (v n) (v (n + 1)) ≠ ε (v (n + 2)) (v (n + 2 + 1)) := by
    intro n hc he
    have hq : q (v n) (v (n + 1)) = q (v (n + 2)) (v (n + 2 + 1)) := by
      rw [(hdata _ (hO n) _ (hO (n + 1)) (hadj n)).2.2,
        (hdata _ (hO (n + 2)) _ (hO (n + 2 + 1)) (hadj (n + 2))).2.2, hc, he]
    have hne : s(v n, v (n + 1)) ≠ s(v (n + 2), v (n + 2 + 1)) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
      · exact n2 n (hv h')
      · exact n3 n (hv h')
    have hadj' := hadj (n + 1)
    rw [e2] at hadj'
    exact (hsep _ (hO n) _ (hO (n + 1)) _ (hO (n + 2)) _ (hO (n + 2 + 1)) (hadj n)
      (hadj (n + 2)) hne hq).2 (v (n + 1)) (by simp) (v (n + 2)) (by simp) hadj'
  exact count_eq_two_of (fun n => c (v n) (v (n + 1))) (fun n => ε (v n) (v (n + 1))) hF1 hF2 i

end CFSG.Combinatorics.HexagonFourEdgePath
