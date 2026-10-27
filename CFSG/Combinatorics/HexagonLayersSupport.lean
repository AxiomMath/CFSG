module

public import CFSG.Combinatorics.CubicBipartiteMooreSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.Combinatorics.HexagonLayers

variable {V : Type*}

section General

variable {G : SimpleGraph V}

theorem col_eq_true_of_adj (col : G.Coloring Bool) {v m : V} (hv : col v = false)
    (h : G.Adj v m) : col m = true := by
  have h' := col.valid h
  rw [hv] at h'
  rcases Bool.eq_false_or_eq_true (col m) with hm | hm
  · exact hm
  · exact absurd hm.symm h'

theorem col_eq_false_of_adj (col : G.Coloring Bool) {v m : V} (hm : col m = true)
    (h : G.Adj v m) : col v = false := by
  have h' := col.valid h
  rw [hm] at h'
  rcases Bool.eq_false_or_eq_true (col v) with hv | hv
  · exact absurd hv h'
  · exact hv

theorem even_dist_of_col_eq (hconn : G.Connected) (col : G.Coloring Bool) {a b : V}
    (h : col a = col b) : Even (G.dist a b) :=
  (even_dist_iff hconn col a b).mpr (by rw [h])

theorem exists_adj_adj_of_dist_eq_two (hconn : G.Connected) {x y : V} (h : G.dist x y = 2) :
    ∃ m, G.Adj x m ∧ G.Adj y m := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  rw [h] at hp
  cases p with
  | nil => simp at hp
  | cons h₁ p' =>
    cases p' with
    | nil => simp at hp
    | cons h₂ p'' =>
      cases p'' with
      | nil => exact ⟨_, h₁, h₂.symm⟩
      | cons _ _ =>
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega

theorem dist_eq_two_of_adj_adj (hconn : G.Connected) (col : G.Coloring Bool) {x y m : V}
    (hxy : x ≠ y) (hc : col x = col y) (hx : G.Adj x m) (hy : G.Adj y m) : G.dist x y = 2 := by
  have hle : G.dist x y ≤ 2 := by
    have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hx (SimpleGraph.Walk.cons hy.symm
      SimpleGraph.Walk.nil))
    simpa using this
  have hne : G.dist x y ≠ 0 := by rwa [Ne, hconn.dist_eq_zero_iff]
  obtain ⟨n, hn⟩ := even_dist_of_col_eq hconn col hc
  omega

theorem exists_of_isCycle_three {W : Type*} {H : SimpleGraph W} {u : W} {c : H.Walk u u}
    (hc : c.IsCycle) (hl : c.length = 3) :
    ∃ a b, H.Adj u a ∧ H.Adj a b ∧ H.Adj b u ∧ a ≠ b ∧ a ≠ u ∧ b ≠ u := by
  have hnd := hc.support_nodup
  cases c with
  | nil => simp at hl
  | cons h₁ c₁ =>
    cases c₁ with
    | nil => simp at hl
    | cons h₂ c₂ =>
      cases c₂ with
      | nil => simp at hl
      | cons h₃ c₃ =>
        cases c₃ with
        | nil =>
          simp at hnd
          exact ⟨_, _, h₁, h₂, h₃, by tauto⟩
        | cons _ _ =>
          simp only [SimpleGraph.Walk.length_cons] at hl
          omega

theorem exists_of_isCycle_four {W : Type*} {H : SimpleGraph W} {u : W} {c : H.Walk u u}
    (hc : c.IsCycle) (hl : c.length = 4) :
    ∃ a b d, H.Adj u a ∧ H.Adj a b ∧ H.Adj b d ∧ H.Adj d u ∧ a ≠ d ∧ b ≠ u := by
  have hnd := hc.support_nodup
  cases c with
  | nil => simp at hl
  | cons h₁ c₁ =>
    cases c₁ with
    | nil => simp at hl
    | cons h₂ c₂ =>
      cases c₂ with
      | nil => simp at hl
      | cons h₃ c₃ =>
        cases c₃ with
        | nil => simp at hl
        | cons h₄ c₄ =>
          cases c₄ with
          | nil =>
            simp at hnd
            exact ⟨_, _, _, h₁, h₂, h₃, h₄, by tauto⟩
          | cons _ _ =>
            simp only [SimpleGraph.Walk.length_cons] at hl
            omega

theorem exists_of_isCycle_five {W : Type*} {H : SimpleGraph W} {u : W} {c : H.Walk u u}
    (hc : c.IsCycle) (hl : c.length = 5) :
    ∃ a b d e, H.Adj u a ∧ H.Adj a b ∧ H.Adj b d ∧ H.Adj d e ∧ H.Adj e u ∧ a ≠ d ∧ a ≠ e ∧
      b ≠ u ∧ b ≠ e ∧ d ≠ u := by
  have hnd := hc.support_nodup
  cases c with
  | nil => simp at hl
  | cons h₁ c₁ =>
    cases c₁ with
    | nil => simp at hl
    | cons h₂ c₂ =>
      cases c₂ with
      | nil => simp at hl
      | cons h₃ c₃ =>
        cases c₃ with
        | nil => simp at hl
        | cons h₄ c₄ =>
          cases c₄ with
          | nil => simp at hl
          | cons h₅ c₅ =>
            cases c₅ with
            | nil =>
              simp at hnd
              exact ⟨_, _, _, _, h₁, h₂, h₃, h₄, h₅, by tauto⟩
            | cons _ _ =>
              simp only [SimpleGraph.Walk.length_cons] at hl
              omega

end General

structure MooreHyp [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  card : Fintype.card V = 126
  conn : G.Connected
  deg : ∀ v, G.degree v = 3
  cyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem nbr_structure (H : MooreHyp G) (col : G.Coloring Bool) {v x : V} {k : ℕ}
    (hk : k + 1 ≤ 5) (hx : G.dist v x = k + 1) :
    ∃ a b c, G.neighborFinset x = {a, b, c} ∧ G.dist v a = k ∧ G.dist v b = k + 2 ∧
      G.dist v c = k + 2 ∧ b ≠ c := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (card_nbrsAt_pred H.cyc H.conn hk hx)
  obtain ⟨b, c, hbc, hbc'⟩ :=
    Finset.card_eq_two.mp (card_nbrsAt_succ H.cyc H.conn col H.deg hk hx)
  have hamem : a ∈ nbrsAt G v x k := by rw [ha]; exact Finset.mem_singleton_self a
  have hbmem : b ∈ nbrsAt G v x (k + 2) := by rw [hbc']; simp
  have hcmem : c ∈ nbrsAt G v x (k + 2) := by rw [hbc']; simp
  rw [Finset.mem_filter] at hamem hbmem hcmem
  refine ⟨a, b, c, ?_, hamem.2, hbmem.2, hcmem.2, hbc⟩
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hy
    rcases dist_adj H.conn col ((SimpleGraph.mem_neighborFinset _ _ _).mp hy) v with h | h
    · have hy' : y ∈ nbrsAt G v x (k + 2) := Finset.mem_filter.mpr ⟨hy, by omega⟩
      rw [hbc', Finset.mem_insert, Finset.mem_singleton] at hy'
      exact Or.inr hy'
    · have hy' : y ∈ nbrsAt G v x k := Finset.mem_filter.mpr ⟨hy, by omega⟩
      rw [ha, Finset.mem_singleton] at hy'
      exact Or.inl hy'
  · rintro (rfl | rfl | rfl)
    exacts [hamem.1, hbmem.1, hcmem.1]

theorem dist_eq_five_of_adj (H : MooreHyp G) (col : G.Coloring Bool) {v x y : V}
    (hx : G.dist v x = 6) (h : G.Adj x y) : G.dist v y = 5 := by
  rcases dist_adj H.conn col h v with h' | h'
  · have := dist_le_six H.cyc H.conn col H.deg H.card v y
    omega
  · omega

theorem neighborFinset_eq (H : MooreHyp G) {m a b c : V} (ha : G.Adj a m) (hb : G.Adj b m)
    (hc : G.Adj c m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.neighborFinset m = {a, b, c} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [SimpleGraph.mem_neighborFinset]
    rcases hy with rfl | rfl | rfl
    exacts [ha.symm, hb.symm, hc.symm]
  · rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg,
      Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩]

theorem nbrs_of_succ (H : MooreHyp G) (col : G.Coloring Bool) {v m x : V} {k : ℕ}
    (hk : k + 1 ≤ 5) (hm : G.dist v m = k + 1) (hxm : G.Adj x m) (hx : G.dist v x = k + 2) :
    ∃ a t, G.neighborFinset m = {x, a, t} ∧ G.dist v a = k ∧ G.dist v t = k + 2 ∧ t ≠ x := by
  obtain ⟨a, b, c, hN, ha, hb, hc, hbc⟩ := nbr_structure H col hk hm
  have hmem : ∀ t ∈ ({a, b, c} : Finset V), G.Adj t m := fun t ht => by
    rw [← hN, SimpleGraph.mem_neighborFinset] at ht
    exact ht.symm
  have hxN : x ∈ ({a, b, c} : Finset V) := by
    rw [← hN, SimpleGraph.mem_neighborFinset]
    exact hxm.symm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxN
  have hxa : x ≠ a := by
    rintro rfl
    omega
  obtain ⟨t, htm, ht, htx⟩ : ∃ t, G.Adj t m ∧ G.dist v t = k + 2 ∧ t ≠ x := by
    rcases hxN with h | h | h
    · exact absurd h hxa
    · exact ⟨c, hmem c (by simp), hc, by rw [h]; exact hbc.symm⟩
    · exact ⟨b, hmem b (by simp), hb, by rw [h]; exact hbc⟩
  have hat : a ≠ t := by
    rintro rfl
    omega
  exact ⟨a, t, neighborFinset_eq H hxm (hmem a (by simp)) htm hxa htx.symm hat, ha, ht, htx⟩

theorem nbrs_of_pred (H : MooreHyp G) (col : G.Coloring Bool) {v m x : V} {k : ℕ}
    (hk : k + 1 ≤ 5) (hm : G.dist v m = k + 1) (hxm : G.Adj x m) (hx : G.dist v x = k) :
    ∃ b c, G.neighborFinset m = {x, b, c} ∧ b ≠ c ∧ G.dist v b = k + 2 ∧ G.dist v c = k + 2 := by
  obtain ⟨a, b, c, hN, ha, hb, hc, hbc⟩ := nbr_structure H col hk hm
  have ham : G.Adj a m := by
    have : a ∈ G.neighborFinset m := by rw [hN]; simp
    exact ((SimpleGraph.mem_neighborFinset _ _ _).mp this).symm
  have hxa : x = a := pred_unique H.cyc H.conn hk hm hxm.symm ham.symm hx ha
  subst hxa
  exact ⟨b, c, hN, hbc, hb, hc⟩

theorem not_three_far_on_line (H : MooreHyp G) (col : G.Coloring Bool) {v m x y z : V}
    (hx : G.dist v x = 6) (hy : G.dist v y = 6) (hz : G.dist v z = 6) (hxm : G.Adj x m)
    (hym : G.Adj y m) (hzm : G.Adj z m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  have hm : G.dist v m = 4 + 1 := dist_eq_five_of_adj H col hx hxm
  have h2 := card_nbrsAt_succ H.cyc H.conn col H.deg (by norm_num) hm
  have hsub : ({x, y, z} : Finset V) ⊆ nbrsAt G v m (4 + 2) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    rcases ht with rfl | rfl | rfl
    exacts [⟨hxm.symm, hx⟩, ⟨hym.symm, hy⟩, ⟨hzm.symm, hz⟩]
  have := Finset.card_le_card hsub
  rw [h2, Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩] at this
  omega

omit [DecidableEq V] in
theorem even_dist_of_far (H : MooreHyp G) (col : G.Coloring Bool) {v x y : V}
    (hx : G.dist v x = 6) (hy : G.dist v y = 6) : Even (G.dist x y) := by
  apply even_dist_of_col_eq H.conn col
  have h1 := (even_dist_iff H.conn col v x).mp (by rw [hx]; decide)
  have h2 := (even_dist_iff H.conn col v y).mp (by rw [hy]; decide)
  rw [Bool.coe_iff_coe] at h1 h2
  rw [← h1, ← h2]

theorem no_far_triangle (H : MooreHyp G) (col : G.Coloring Bool) {v x y z : V}
    (hx : G.dist v x = 6) (hy : G.dist v y = 6) (hz : G.dist v z = 6) (hxy : G.dist x y = 2)
    (hyz : G.dist y z = 2) (hzx : G.dist z x = 2) : False := by
  obtain ⟨m, hym, hzm⟩ := exists_adj_adj_of_dist_eq_two H.conn hyz
  have hne : ∀ {a b : V}, G.dist a b = 2 → a ≠ b := by
    rintro a b h rfl
    rw [SimpleGraph.dist_self] at h
    omega
  by_cases hxm : G.Adj x m
  · exact not_three_far_on_line H col hx hy hz hxm hym hzm (hne hxy) (hne hzx).symm (hne hyz)
  · have hd : G.dist x m = 2 + 1 := by
      rcases dist_adj H.conn col hym x with h | h
      · omega
      · exact absurd (SimpleGraph.dist_eq_one_iff_adj.mp (by omega)) hxm
    have hzx' : G.dist x z = 2 := by rw [SimpleGraph.dist_comm]; exact hzx
    exact hne hyz (pred_unique H.cyc H.conn (by norm_num) hd hym.symm hzm.symm hxy hzx')

omit [DecidableEq V] in
theorem dist_eq_four_of_far (H : MooreHyp G) (col : G.Coloring Bool) {v x y z : V}
    (hx : G.dist v x = 6) (hz : G.dist v z = 6) (hxy : G.dist x y = 2) (hyz : G.dist y z = 2)
    (hxz : x ≠ z) (hxz' : G.dist x z ≠ 2) : G.dist x z = 4 := by
  have hle : G.dist x z ≤ G.dist x y + G.dist y z := H.conn.dist_triangle
  have hne : G.dist x z ≠ 0 := by rwa [Ne, H.conn.dist_eq_zero_iff]
  obtain ⟨n, hn⟩ := even_dist_of_far H col hx hz
  omega

theorem line_eq_of_dist_le_three (H : MooreHyp G) (col : G.Coloring Bool) {x y m m' : V}
    (hxy : G.dist x y = 4) (hm : G.Adj y m) (hm' : G.Adj y m') (hxm : G.dist x m ≤ 3)
    (hxm' : G.dist x m' ≤ 3) : m = m' := by
  have h3 : ∀ {n : V}, G.Adj y n → G.dist x n ≤ 3 → G.dist x n = 3 := by
    intro n hn hle
    rcases dist_adj H.conn col hn x with h | h <;> omega
  exact pred_unique H.cyc H.conn (k := 3) (by norm_num) hxy hm hm' (h3 hm hxm) (h3 hm' hxm')

theorem no_far_square (H : MooreHyp G) (col : G.Coloring Bool) {v x₀ x₁ x₂ x₃ : V}
    (h₀ : G.dist v x₀ = 6) (h₁ : G.dist v x₁ = 6) (h₂ : G.dist v x₂ = 6) (h₃ : G.dist v x₃ = 6)
    (h01 : G.dist x₀ x₁ = 2) (h12 : G.dist x₁ x₂ = 2) (h23 : G.dist x₂ x₃ = 2)
    (h30 : G.dist x₃ x₀ = 2) (h02 : x₀ ≠ x₂) (h13 : x₁ ≠ x₃) : False := by
  have hd02 : G.dist x₀ x₂ = 4 := dist_eq_four_of_far H col h₀ h₂ h01 h12 h02
    (fun h => no_far_triangle H col h₀ h₁ h₂ h01 h12 (by rw [SimpleGraph.dist_comm]; exact h))
  obtain ⟨m, hm1, hm2⟩ := exists_adj_adj_of_dist_eq_two H.conn h12
  obtain ⟨m', hm2', hm3⟩ := exists_adj_adj_of_dist_eq_two H.conn h23
  have hle : G.dist x₀ m ≤ 3 := by
    have h : G.dist x₀ m ≤ G.dist x₀ x₁ + G.dist x₁ m := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hm1] at h
    omega
  have hle' : G.dist x₀ m' ≤ 3 := by
    have h : G.dist x₀ m' ≤ G.dist x₀ x₃ + G.dist x₃ m' := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hm3, SimpleGraph.dist_comm (u := x₀) (v := x₃),
      h30] at h
    omega
  have hmm := line_eq_of_dist_le_three H col hd02 hm2 hm2' hle hle'
  subst hmm
  have hne : ∀ {a b : V}, G.dist a b = 2 → a ≠ b := by
    rintro a b h rfl
    rw [SimpleGraph.dist_self] at h
    omega
  exact not_three_far_on_line H col h₁ h₂ h₃ hm1 hm2 hm3 (hne h12) h13 (hne h23)

theorem no_far_pentagon (H : MooreHyp G) (col : G.Coloring Bool) {v x₀ x₁ x₂ x₃ x₄ : V}
    (h₀ : G.dist v x₀ = 6) (h₁ : G.dist v x₁ = 6) (h₂ : G.dist v x₂ = 6) (h₃ : G.dist v x₃ = 6)
    (h₄ : G.dist v x₄ = 6) (h01 : G.dist x₀ x₁ = 2) (h12 : G.dist x₁ x₂ = 2)
    (h23 : G.dist x₂ x₃ = 2) (h34 : G.dist x₃ x₄ = 2) (h40 : G.dist x₄ x₀ = 2) (h02 : x₀ ≠ x₂)
    (h03 : x₀ ≠ x₃) (h13 : x₁ ≠ x₃) : False := by
  have hd02 : G.dist x₀ x₂ = 4 := dist_eq_four_of_far H col h₀ h₂ h01 h12 h02
    (fun h => no_far_triangle H col h₀ h₁ h₂ h01 h12 (by rw [SimpleGraph.dist_comm]; exact h))
  have h04 : G.dist x₀ x₄ = 2 := by rw [SimpleGraph.dist_comm]; exact h40
  have h43 : G.dist x₄ x₃ = 2 := by rw [SimpleGraph.dist_comm]; exact h34
  have hd03 : G.dist x₀ x₃ = 4 := dist_eq_four_of_far H col h₀ h₃ h04 h43 h03
    (fun h => no_far_triangle H col h₀ h₃ h₄ h h34 h40)
  obtain ⟨m, hm1, hm2⟩ := exists_adj_adj_of_dist_eq_two H.conn h12
  obtain ⟨m', hm2', hm3⟩ := exists_adj_adj_of_dist_eq_two H.conn h23
  have hle : G.dist x₀ m ≤ 3 := by
    have h : G.dist x₀ m ≤ G.dist x₀ x₁ + G.dist x₁ m := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hm1] at h
    omega
  have hne : ∀ {a b : V}, G.dist a b = 2 → a ≠ b := by
    rintro a b h rfl
    rw [SimpleGraph.dist_self] at h
    omega
  have hle' : G.dist x₀ m' ≤ 3 := by
    rcases dist_adj H.conn col hm2' x₀ with h | h
    · exfalso
      exact hne h23 (pred_unique H.cyc H.conn (k := 4) (by norm_num) (by omega) hm2'.symm
        hm3.symm hd02 hd03)
    · omega
  have hmm := line_eq_of_dist_le_three H col hd02 hm2 hm2' hle hle'
  subst hmm
  exact not_three_far_on_line H col h₁ h₂ h₃ hm1 hm2 hm3 (hne h12) h13 (hne h23)

theorem exists_unique_lower (H : MooreHyp G) (col : G.Coloring Bool) {v z : V}
    (hz : G.dist v z = 4) :
    ∃ q, G.dist z q = 2 ∧ G.dist v q = 2 ∧ ∀ q', G.dist z q' = 2 → G.dist v q' = 2 → q' = q := by
  obtain ⟨m, hzm, hm⟩ := pred_exists H.conn (show G.dist v z = 3 + 1 from hz)
  obtain ⟨q, hmq, hq⟩ := pred_exists H.conn (show G.dist v m = 2 + 1 from hm)
  have hzq : G.dist z q = 2 := by
    have h1 : G.dist z q ≤ G.dist z m + G.dist m q := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hzm, SimpleGraph.dist_eq_one_iff_adj.mpr hmq] at h1
    have h2 : G.dist v z ≤ G.dist v q + G.dist q z := H.conn.dist_triangle
    rw [SimpleGraph.dist_comm (u := q)] at h2
    omega
  refine ⟨q, hzq, hq, fun q' hzq' hq' => ?_⟩
  have hline : ∀ {t : V}, G.dist z t = 2 → G.dist v t = 2 →
      ∃ n, G.Adj z n ∧ G.Adj t n ∧ G.dist v n = 2 + 1 := by
    intro t hzt hvt
    obtain ⟨n, hzn, htn⟩ := exists_adj_adj_of_dist_eq_two H.conn hzt
    refine ⟨n, hzn, htn, ?_⟩
    have h1 : G.dist v n ≤ G.dist v t + G.dist t n := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr htn] at h1
    rcases dist_adj H.conn col hzn v with h | h <;> omega
  obtain ⟨n, hzn, hqn, hn⟩ := hline hzq hq
  obtain ⟨n', hzn', hqn', hn'⟩ := hline hzq' hq'
  have hnn : n = n' := pred_unique H.cyc H.conn (k := 3) (by norm_num) hz hzn hzn' hn hn'
  subst hnn
  exact pred_unique H.cyc H.conn (by norm_num) hn hqn'.symm hqn.symm hq' hq

theorem dist_four_six (H : MooreHyp G) (col : G.Coloring Bool) {w x l a b : V}
    (hx : G.dist x w = 6) (hwl : G.Adj w l) (hal : G.Adj a l) (hbl : G.Adj b l) (hab : a ≠ b)
    (haw : a ≠ w) (hbw : b ≠ w) :
    (G.dist x a = 4 ∧ G.dist x b = 6) ∨ (G.dist x a = 6 ∧ G.dist x b = 4) := by
  have hl : G.dist x l = 4 + 1 := dist_eq_five_of_adj H col hx hwl
  have h46 : ∀ {t : V}, G.Adj t l → G.dist x t = 4 ∨ G.dist x t = 6 := by
    intro t ht
    rcases dist_adj H.conn col ht.symm x with h | h <;> omega
  rcases h46 hal with ha | ha <;> rcases h46 hbl with hb | hb
  · exact absurd (pred_unique H.cyc H.conn (by norm_num) hl hal.symm hbl.symm ha hb) hab
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact (not_three_far_on_line H col hx ha hb hwl hal hbl haw.symm hbw.symm hab).elim

omit [DecidableEq V] in
theorem dist_eq_four_of_lower (H : MooreHyp G) {w x m z q : V} (hx : G.dist w x = 6)
    (hxm : G.Adj x m) (hzm : G.Adj z m) (hq : G.dist w q = 2) (hzq : G.dist z q = 2) :
    G.dist x q = 4 := by
  have h1 : G.dist x q ≤ G.dist x z + G.dist z q := H.conn.dist_triangle
  have h2 : G.dist x z ≤ G.dist x m + G.dist m z := H.conn.dist_triangle
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxm, SimpleGraph.dist_eq_one_iff_adj.mpr hzm.symm]
    at h2
  have h3 : G.dist w x ≤ G.dist w q + G.dist q x := H.conn.dist_triangle
  rw [SimpleGraph.dist_comm (u := q)] at h3
  omega

theorem line_eq_of_lower (H : MooreHyp G) (col : G.Coloring Bool) {w x m m' z z' q : V}
    (hx : G.dist w x = 6) (hxm : G.Adj x m) (hzm : G.Adj z m) (hxm' : G.Adj x m')
    (hzm' : G.Adj z' m') (hq : G.dist w q = 2) (hzq : G.dist z q = 2) (hzq' : G.dist z' q = 2) :
    m = m' := by
  have hqx : G.dist q x = 4 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_four_of_lower H hx hxm hzm hq hzq
  have hle : ∀ {n t : V}, G.Adj t n → G.dist t q = 2 → G.dist q n ≤ 3 := by
    intro n t htn htq
    have h1 : G.dist q n ≤ G.dist q t + G.dist t n := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr htn, SimpleGraph.dist_comm (u := q) (v := t)] at h1
    omega
  exact line_eq_of_dist_le_three H col hqx hxm hxm' (hle hzm hzq) (hle hzm' hzq')

theorem exists_far_edge (H : MooreHyp G) (col : G.Coloring Bool) {w x q : V}
    (hx : G.dist w x = 6) (hq : G.dist w q = 2) (hxq : G.dist x q = 4) :
    ∃ m y z, G.Adj x m ∧ G.Adj y m ∧ G.Adj z m ∧ y ≠ x ∧ G.dist w y = 6 ∧ G.dist w z = 4 ∧
      G.dist z q = 2 := by
  obtain ⟨m, hxm, hm⟩ := pred_exists H.conn
    (show G.dist q x = 3 + 1 by rw [SimpleGraph.dist_comm]; exact hxq)
  obtain ⟨z, hmz, hz⟩ := pred_exists H.conn (show G.dist q m = 2 + 1 from hm)
  have hwz : G.dist w z = 4 := by
    have h1 : G.dist w z ≤ G.dist w q + G.dist q z := H.conn.dist_triangle
    have h2 : G.dist w x ≤ G.dist w z + G.dist z x := H.conn.dist_triangle
    have h3 : G.dist z x ≤ G.dist z m + G.dist m x := H.conn.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hmz.symm, SimpleGraph.dist_eq_one_iff_adj.mpr
      hxm.symm] at h3
    omega
  have hwm : G.dist w m = 4 + 1 := dist_eq_five_of_adj H col hx hxm
  obtain ⟨a, y, hN, -, hy, hyx⟩ := nbrs_of_succ H col (by norm_num) hwm hxm hx
  have hym : G.Adj y m := by
    have : y ∈ G.neighborFinset m := by rw [hN]; simp
    exact ((SimpleGraph.mem_neighborFinset _ _ _).mp this).symm
  exact ⟨m, y, z, hxm, hym, hmz.symm, hyx, hy, hwz, by rw [SimpleGraph.dist_comm]; exact hz⟩

theorem eq_of_dist_four_four (H : MooreHyp G) (col : G.Coloring Bool) {w x y m z q₀ q : V}
    (hx : G.dist w x = 6) (hy : G.dist w y = 6) (hxy : x ≠ y) (hxm : G.Adj x m)
    (hym : G.Adj y m) (hzm : G.Adj z m) (hz : G.dist w z = 4) (hq₀ : G.dist w q₀ = 2)
    (hzq₀ : G.dist z q₀ = 2) (hq : G.dist w q = 2) (hxq : G.dist x q = 4)
    (hyq : G.dist y q = 4) : q = q₀ := by
  have hqx : G.dist q x = 4 := by rw [SimpleGraph.dist_comm]; exact hxq
  have hqy : G.dist q y = 4 := by rw [SimpleGraph.dist_comm]; exact hyq
  have hqm : G.dist q m = 2 + 1 := by
    rcases dist_adj H.conn col hxm q with h | h
    · exact absurd (pred_unique H.cyc H.conn (k := 4) (by norm_num) (by omega) hxm.symm
        hym.symm hqx hqy) hxy
    · omega
  obtain ⟨t, hmt, ht⟩ := pred_exists H.conn hqm
  have hN : G.neighborFinset m = {x, y, z} :=
    neighborFinset_eq H hxm hym hzm hxy (by rintro rfl; omega) (by rintro rfl; omega)
  have htN : t ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr hmt
  rw [hN] at htN
  simp only [Finset.mem_insert, Finset.mem_singleton] at htN
  obtain ⟨q₁, -, -, huniq⟩ := exists_unique_lower H col hz
  rcases htN with rfl | rfl | rfl
  · omega
  · omega
  · rw [huniq q (by rw [SimpleGraph.dist_comm]; exact ht) hq, huniq q₀ hzq₀ hq₀]

end CFSG.Combinatorics.HexagonLayers
