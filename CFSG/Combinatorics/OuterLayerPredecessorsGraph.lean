module

public import CFSG.Combinatorics.OuterLayerPredecessorsSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.OuterLayer

section General

theorem copies_adj (ι : Type*) {X : Type*} (H : SimpleGraph X) {a b : ι × X} :
    (copies ι H).Adj a b ↔ a.1 = b.1 ∧ H.Adj a.2 b.2 :=
  Iff.rfl

theorem copies_eq_boxProd (ι : Type*) {X : Type*} (H : SimpleGraph X) :
    copies ι H = (⊥ : SimpleGraph ι) □ H := by
  ext a b
  rw [copies_adj, SimpleGraph.boxProd_adj]
  simp only [SimpleGraph.bot_adj, false_and, false_or]
  exact and_comm

theorem fin_two_injective {α : Type*} {f : Fin 2 → α} (h : f 0 ≠ f 1) : Function.Injective f := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd hab h
  · exact absurd hab.symm h
  · rfl

end General

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}}

theorem existsUnique_pred (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = i) :
    ∃! s : {v : V // col v = false}, (pointGraph G col).dist w s = i - 1 ∧
      (pointGraph G col).Adj x s := by
  obtain ⟨m, xm, hmchar, ⟨a, t, hN, ha, ht, -⟩, -⟩ := inner_layer_lines H col w hi x hx
  have ham : G.Adj (a : V) m :=
    ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have hxa : (x : V) ≠ a := fun e => by
    rw [Subtype.ext e] at hx
    omega
  refine ⟨a, ⟨ha, (point_adj_iff H.conn col x a).mpr
    (dist_eq_two_of_adj_adj H.conn col hxa (x.2.trans a.2.symm) xm ham)⟩, fun s ⟨hs, hxs⟩ => ?_⟩
  obtain ⟨n, xn, sn⟩ :=
    exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col x s).mp hxs)
  have hnm : n = m := (hmchar n xn).mp ⟨s, sn, hs⟩
  rw [hnm] at sn
  have hsN : (s : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr sn.symm
  rw [hN] at hsN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsN
  rcases hsN with h | h | h
  · exact absurd (Subtype.ext h).symm hxs.ne
  · exact Subtype.ext h
  · rw [Subtype.ext h] at hs
    omega

theorem outerRelGraph_adj_iff (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {x y : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}} :
    (outerRelGraph G col w i).Adj x y ↔ x ≠ y ∧ ∃ s : {v : V // col v = false},
      (pointGraph G col).dist w s = i - 1 ∧ (pointGraph G col).Adj x s ∧
      (pointGraph G col).Adj y s ∧ ∀ m m' : V, G.Adj ((x : {v : V // col v = false}) : V) m →
        G.Adj (s : V) m → G.Adj ((y : {v : V // col v = false}) : V) m' → G.Adj (s : V) m' →
          m ≠ m' := by
  have hne : ∀ {a b : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}},
      a ≠ b → (a : {v : V // col v = false}) ≠ b := fun h e => h (Subtype.ext e)
  rw [outerRelGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, hR | hR⟩
    · exact ⟨hxy, exists_pred_of_outerRel H hi x.2 y.2 (hne hxy) hR⟩
    · obtain ⟨s, hs, hys, hxs, hl⟩ := exists_pred_of_outerRel H hi y.2 x.2 (hne hxy.symm) hR
      exact ⟨hxy, s, hs, hxs, hys, fun m m' xm sm ym' sm' => (hl m' m ym' sm' xm sm).symm⟩
  · rintro ⟨hxy, s, hs, hxs, hys, hl⟩
    exact ⟨hxy, Or.inl (outerRel_of_pred H hi x.2 y.2 hs hxs hys hl)⟩

theorem outerRelGraph_one_iso (H : MooreHyp G) {ℓ : Fin 3 → V} (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj (w : V) (ℓ i)) {p : Fin 3 → Fin 2 → {v : V // col v = false}}
    (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i)) (hpw : ∀ i e, p i e ≠ w)
    (hp : ∀ i, Function.Injective (p i)) :
    ∃ φ : SimpleGraph.completeEquipartiteGraph 3 2 ≃g outerRelGraph G col w 1,
      ∀ j e, ((φ (j, e) : {v : V // col v = false}) : V) = p j e := by
  have hd := point_dist_eq_iff H.conn col
  have hlab : ∀ j e, (pointGraph G col).dist w (p j e) = 1 := fun j e =>
    (hd w (p j e) 1).mpr (dist_label H col hwℓ hpℓ hpw j e)
  let f : Fin 3 × Fin 2 → {x : {v : V // col v = false} // (pointGraph G col).dist w x = 1} :=
    fun je => ⟨p je.1 je.2, hlab _ _⟩
  have hinj : Function.Injective f := by
    rintro ⟨j, e⟩ ⟨j', e'⟩ h
    obtain ⟨h1, h2⟩ := label_injective H col hℓ hwℓ hpℓ hpw hp (congrArg Subtype.val h)
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨j, e, hje⟩ := exists_label H col hℓ hwℓ hpℓ hpw hp ((hd w x 1).mp hx)
    exact ⟨(j, e), Subtype.ext (Subtype.ext hje)⟩
  have hline : ∀ j e m, G.Adj (p j e : V) m → G.Adj (w : V) m → m = ℓ j := fun j e m h1 h2 =>
    pred_unique H.cyc H.conn (k := 1) (by norm_num)
      (show G.dist (w : V) (p j e) = 1 + 1 from dist_label H col hwℓ hpℓ hpw j e) h1 (hpℓ j e)
      (SimpleGraph.dist_eq_one_iff_adj.mpr h2) (SimpleGraph.dist_eq_one_iff_adj.mpr (hwℓ j))
  have hadjw : ∀ j e, (pointGraph G col).Adj (p j e) w := fun j e =>
    (point_adj_iff H.conn col _ _).mpr (by
      rw [SimpleGraph.dist_comm]
      exact dist_label H col hwℓ hpℓ hpw j e)
  have hadj : ∀ a b, (outerRelGraph G col w 1).Adj (f a) (f b) ↔
      (SimpleGraph.completeEquipartiteGraph 3 2).Adj a b := by
    rintro ⟨j, e⟩ ⟨j', e'⟩
    rw [outerRelGraph_adj_iff H (Or.inl rfl), SimpleGraph.completeEquipartiteGraph_adj]
    constructor
    · rintro ⟨-, s, hs, -, -, hl⟩ hjj
      have hsw : s = w := Subtype.ext (H.conn.dist_eq_zero_iff.mp (by
        have := (hd w s 0).mp hs
        omega)).symm
      rw [hsw] at hl
      exact hl (ℓ j) (ℓ j') (hpℓ j e) (hwℓ j) (hpℓ j' e') (hwℓ j') (congrArg ℓ hjj)
    · intro hjj
      refine ⟨fun h => hjj (label_injective H col hℓ hwℓ hpℓ hpw hp
        (congrArg Subtype.val h)).1, w, by simp, hadjw j e, hadjw j' e',
        fun m m' h1 h2 h3 h4 => ?_⟩
      rw [hline j e m h1 h2, hline j' e' m' h3 h4]
      exact hℓ.ne hjj
  exact ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun {a b} => hadj a b⟩, fun j e => rfl⟩

theorem exists_outward_lines (H : MooreHyp G) {s : {v : V // col v = false}}
    (hs : (pointGraph G col).dist w s = 1) :
    ∃ (L : Fin 2 → V) (q : Fin 2 → Fin 2 → {v : V // col v = false}), L 0 ≠ L 1 ∧
      (∀ j, G.Adj (s : V) (L j)) ∧ (∀ j e, G.Adj (q j e : V) (L j)) ∧ (∀ j, q j 0 ≠ q j 1) ∧
      (∀ j e, (pointGraph G col).dist w (q j e) = 2) ∧
      ∀ x : {v : V // col v = false}, (pointGraph G col).dist w x = 2 →
        (pointGraph G col).Adj x s → ∃ j e, q j e = x := by
  have hd := point_dist_eq_iff H.conn col
  have hs2 : G.dist (w : V) s = 1 + 1 := (hd w s 1).mp hs
  obtain ⟨a, b, c, hN, ha, hb, hc, hbc⟩ := nbr_structure H col (by norm_num) hs2
  have hsb : G.Adj (s : V) b := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
  have hsc : G.Adj (s : V) c := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
  have hpts : ∀ {n : V}, G.Adj (s : V) n → G.dist (w : V) n = 1 + 2 →
      ∃ q : Fin 2 → {v : V // col v = false},
        G.neighborFinset n = {(s : V), (q 0 : V), (q 1 : V)} ∧ q 0 ≠ q 1 ∧
          ∀ e, G.Adj (q e : V) n ∧ (pointGraph G col).dist w (q e) = 2 := by
    intro n hsn hn
    obtain ⟨z₀, z₁, hNn, hz, hz₀, hz₁⟩ :=
      nbrs_of_pred H col (k := 2) (by norm_num) (by omega) hsn (by omega)
    have hncol : col n = true := col_eq_true_of_adj col s.2 hsn
    have hz₀n : G.Adj z₀ n := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNn]; simp)).symm
    have hz₁n : G.Adj z₁ n := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNn]; simp)).symm
    refine ⟨![⟨z₀, col_eq_false_of_adj col hncol hz₀n⟩, ⟨z₁, col_eq_false_of_adj col hncol hz₁n⟩],
      by simpa using hNn, fun h => hz (by simpa using congrArg Subtype.val h), ?_⟩
    refine Fin.forall_fin_two.mpr ⟨⟨hz₀n, (hd w _ 2).mpr ?_⟩, ⟨hz₁n, (hd w _ 2).mpr ?_⟩⟩
    · change G.dist (w : V) z₀ = 2 * 2
      omega
    · change G.dist (w : V) z₁ = 2 * 2
      omega
  obtain ⟨qb, hNb, hqb, hqb'⟩ := hpts hsb hb
  obtain ⟨qc, hNc, hqc, hqc'⟩ := hpts hsc hc
  refine ⟨![b, c], ![qb, qc], by simpa using hbc, Fin.forall_fin_two.mpr ⟨hsb, hsc⟩,
    Fin.forall_fin_two.mpr ⟨fun e => (hqb' e).1, fun e => (hqc' e).1⟩,
    Fin.forall_fin_two.mpr ⟨hqb, hqc⟩,
    Fin.forall_fin_two.mpr ⟨fun e => (hqb' e).2, fun e => (hqc' e).2⟩, ?_⟩
  intro x hx hxs
  obtain ⟨n, xn, sn⟩ :=
    exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col x s).mp hxs)
  have hnN : n ∈ G.neighborFinset (s : V) := (SimpleGraph.mem_neighborFinset _ _ _).mpr sn
  rw [hN] at hnN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnN
  have hx4 : G.dist (w : V) x = 4 := (hd w x 2).mp hx
  have hxs' : (x : V) ≠ s := fun e => hxs.ne (Subtype.ext e)
  have hon : ∀ {n' : V} {q : Fin 2 → {v : V // col v = false}},
      G.neighborFinset n' = {(s : V), (q 0 : V), (q 1 : V)} → G.Adj (x : V) n' →
        ∃ e, q e = x := by
    intro n' q hN' hxn'
    have hxN : (x : V) ∈ G.neighborFinset n' :=
      (SimpleGraph.mem_neighborFinset _ _ _).mpr hxn'.symm
    rw [hN'] at hxN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxN
    rcases hxN with h | h | h
    · exact absurd h hxs'
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩
  rcases hnN with h | h | h
  ·
    exfalso
    rw [h] at xn
    have h1 := H.conn.dist_triangle (u := (w : V)) (v := a) (w := (x : V))
    rw [SimpleGraph.dist_comm (u := a), SimpleGraph.dist_eq_one_iff_adj.mpr xn] at h1
    omega
  · rw [h] at xn
    obtain ⟨e, he⟩ := hon hNb xn
    exact ⟨0, e, he⟩
  · rw [h] at xn
    obtain ⟨e, he⟩ := hon hNc xn
    exact ⟨1, e, he⟩

theorem outerRelGraph_two_iso (H : MooreHyp G) :
    ∃ φ : copies {s : {v : V // col v = false} // (pointGraph G col).dist w s = 1}
        (SimpleGraph.completeEquipartiteGraph 2 2) ≃g outerRelGraph G col w 2,
      (∀ (s : {s : {v : V // col v = false} // (pointGraph G col).dist w s = 1})
        (x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = 2}),
        (pointGraph G col).Adj (x : {v : V // col v = false}) s ↔ ∃ a, φ (s, a) = x) ∧
      ∀ (s : {s : {v : V // col v = false} // (pointGraph G col).dist w s = 1}) (j : Fin 2),
        ∃ m : V, G.Adj ((s : {v : V // col v = false}) : V) m ∧
          ∀ e, G.Adj ((φ (s, (j, e)) : {v : V // col v = false}) : V) m := by
  choose L q hL01 hsL hqL hq01 hq2 hcover using
    fun s : {s : {v : V // col v = false} // (pointGraph G col).dist w s = 1} =>
      exists_outward_lines H s.2
  have hqs : ∀ s j e, (pointGraph G col).Adj (q s j e) s := fun s j e =>
    (point_adj_iff H.conn col _ _).mpr (dist_eq_two_of_adj_adj H.conn col
      (fun h => by
        have := hq2 s j e
        rw [Subtype.ext h, s.2] at this
        omega)
      ((q s j e).2.trans (s : {v : V // col v = false}).2.symm) (hqL s j e) (hsL s j))
  have hline : ∀ s j e m, G.Adj (q s j e : V) m →
      G.Adj ((s : {v : V // col v = false}) : V) m → m = L s j := fun s j e m h1 h2 =>
    (exists_unique_common_line H col (hqs s j e)).unique ⟨h1, h2⟩ ⟨hqL s j e, hsL s j⟩
  have hpred : ∀ s j e (t : {v : V // col v = false}), (pointGraph G col).dist w t = 1 →
      (pointGraph G col).Adj (q s j e) t → t = s := fun s j e t ht hqt =>
    (existsUnique_pred H (Or.inr rfl) (hq2 s j e)).unique ⟨ht, hqt⟩ ⟨s.2, hqs s j e⟩
  have hLinj : ∀ s, Function.Injective (L s) := fun s => fin_two_injective (hL01 s)
  have hqinj : ∀ s j, Function.Injective (q s j) := fun s j => fin_two_injective (hq01 s j)
  let f : {s : {v : V // col v = false} // (pointGraph G col).dist w s = 1} × (Fin 2 × Fin 2) →
      {x : {v : V // col v = false} // (pointGraph G col).dist w x = 2} :=
    fun a => ⟨q a.1 a.2.1 a.2.2, hq2 _ _ _⟩
  have hinj : Function.Injective f := by
    rintro ⟨s, j, e⟩ ⟨s', j', e'⟩ h
    have h' : q s j e = q s' j' e' := congrArg Subtype.val h
    have hss : s = s' :=
      Subtype.ext (hpred s' j' e' s s.2 (by rw [← h']; exact hqs s j e))
    cases hss
    have hjj : j = j' :=
      hLinj s (hline s j' e' (L s j) (by rw [← h']; exact hqL s j e) (hsL s j))
    cases hjj
    rw [hqinj s j h']
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨t, ⟨ht, hxt⟩, -⟩ := existsUnique_pred H (Or.inr rfl) hx
    obtain ⟨j, e, hje⟩ := hcover ⟨t, ht⟩ x hx hxt
    exact ⟨(⟨t, ht⟩, j, e), Subtype.ext hje⟩
  have hadj : ∀ a b, (outerRelGraph G col w 2).Adj (f a) (f b) ↔
      (copies _ (SimpleGraph.completeEquipartiteGraph 2 2)).Adj a b := by
    rintro ⟨s, j, e⟩ ⟨s', j', e'⟩
    rw [outerRelGraph_adj_iff H (Or.inr rfl)]
    simp only [copies_adj, SimpleGraph.completeEquipartiteGraph_adj]
    constructor
    · rintro ⟨-, t, ht, hxt, hyt, hl⟩
      have h1 : t = s := hpred s j e t ht hxt
      have h2 : t = s' := hpred s' j' e' t ht hyt
      have hss : s = s' := Subtype.ext (h1.symm.trans h2)
      cases hss
      rw [h1] at hl
      exact ⟨rfl, fun hjj => hl (L s j) (L s j') (hqL s j e) (hsL s j) (hqL s j' e') (hsL s j')
        (congrArg (L s) hjj)⟩
    · rintro ⟨hss, hjj⟩
      cases hss
      refine ⟨fun h => hjj (congrArg (fun a => a.2.1) (hinj h)), s, s.2, hqs s j e, hqs s j' e',
        fun m m' h1 h2 h3 h4 => ?_⟩
      rw [hline s j e m h1 h2, hline s j' e' m' h3 h4]
      exact (hLinj s).ne hjj
  refine ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun {a b} => hadj a b⟩,
    fun s x => ⟨fun h => ?_, ?_⟩, fun s j => ⟨L s j, hsL s j, fun e => hqL s j e⟩⟩
  · obtain ⟨j, e, hje⟩ := hcover s x x.2 h
    exact ⟨(j, e), Subtype.ext hje⟩
  · rintro ⟨⟨j, e⟩, rfl⟩
    exact hqs s j e

theorem exists_outward_point (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2)
    {s : {v : V // col v = false}} (hs : (pointGraph G col).dist w s = i - 1) (m : V) :
    ∃ (z : {v : V // col v = false}) (L : V), (pointGraph G col).dist w z = i ∧
      (pointGraph G col).Adj z s ∧ G.Adj (z : V) L ∧ G.Adj (s : V) L ∧ L ≠ m := by
  have hd := point_dist_eq_iff H.conn col
  have hs' : G.dist (w : V) s = 2 * (i - 1) := (hd w s _).mp hs
  obtain ⟨b, c, hbc, hsb, hsc, hb, hc⟩ : ∃ b c : V, b ≠ c ∧ G.Adj (s : V) b ∧
      G.Adj (s : V) c ∧ G.dist (w : V) b = G.dist (w : V) s + 1 ∧
        G.dist (w : V) c = G.dist (w : V) s + 1 := by
    rcases hi with rfl | rfl
    · have hsw : (w : V) = s := H.conn.dist_eq_zero_iff.mp (by omega)
      obtain ⟨b, c, d, hbc, -, -, hN⟩ := Finset.card_eq_three.mp
        (show (G.neighborFinset (s : V)).card = 3 by
          rw [SimpleGraph.card_neighborFinset_eq_degree, H.deg])
      have hsb : G.Adj (s : V) b := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      have hsc : G.Adj (s : V) c := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      refine ⟨b, c, hbc, hsb, hsc, ?_, ?_⟩
      · rw [hsw, SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr hsb]
      · rw [hsw, SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr hsc]
    · obtain ⟨a, b, c, hN, -, hb, hc, hbc⟩ := nbr_structure H col (k := 1) (by norm_num)
        (by omega : G.dist (w : V) s = 1 + 1)
      have hsb : G.Adj (s : V) b := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      have hsc : G.Adj (s : V) c := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
      exact ⟨b, c, hbc, hsb, hsc, by omega, by omega⟩
  obtain ⟨L, hsL, hL, hLm⟩ : ∃ L : V, G.Adj (s : V) L ∧
      G.dist (w : V) L = G.dist (w : V) s + 1 ∧ L ≠ m := by
    by_cases hbm : b = m
    · exact ⟨c, hsc, hc, fun h => hbc (hbm.trans h.symm)⟩
    · exact ⟨b, hsb, hb, hbm⟩
  obtain ⟨z, _, hNL, -, hz, -⟩ :=
    nbrs_of_pred H col (k := G.dist (w : V) s) (by omega) hL hsL rfl
  have hzL : G.Adj z L := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hNL]; simp)).symm
  have hzcol : col z = false := col_eq_false_of_adj col (col_eq_true_of_adj col s.2 hsL) hzL
  refine ⟨⟨z, hzcol⟩, L, (hd w _ i).mpr (show G.dist (w : V) z = 2 * i by omega), ?_, hzL, hsL,
    hLm⟩
  refine (point_adj_iff H.conn col _ s).mpr (dist_eq_two_of_adj_adj H.conn col (fun e => ?_)
    (hzcol.trans s.2.symm) hzL hsL)
  have e' : z = (s : V) := e
  rw [e'] at hz
  omega

theorem outerRelGraph_components (H : MooreHyp G) {i : ℕ} (hi : i = 1 ∨ i = 2) :
    ∃ e : (outerRelGraph G col w i).ConnectedComponent ≃
        {s : {v : V // col v = false} // (pointGraph G col).dist w s = i - 1},
      (∀ x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i},
        (pointGraph G col).Adj (x : {v : V // col v = false})
          (e ((outerRelGraph G col w i).connectedComponentMk x))) ∧
      ∀ x y : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}, x ≠ y →
        (outerRelGraph G col w i).connectedComponentMk x =
          (outerRelGraph G col w i).connectedComponentMk y →
        (¬ (outerRelGraph G col w i).Adj x y ↔ ∃ m : V, ¬ IsOuterLine G col w i m ∧
          G.neighborFinset m = {((e ((outerRelGraph G col w i).connectedComponentMk x) :
            {v : V // col v = false}) : V), ((x : {v : V // col v = false}) : V),
            ((y : {v : V // col v = false}) : V)}) := by
  have hu := fun x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i} =>
    existsUnique_pred H hi x.2
  choose pr hpr using fun x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i} =>
    (hu x).exists
  have hπ : ∀ (x : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i})
      (t : {v : V // col v = false}), (pointGraph G col).dist w t = i - 1 →
      (pointGraph G col).Adj (x : {v : V // col v = false}) t → t = pr x :=
    fun x t ht hxt => (hu x).unique ⟨ht, hxt⟩ (hpr x)
  let π : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i} →
      {s : {v : V // col v = false} // (pointGraph G col).dist w s = i - 1} :=
    fun x => ⟨pr x, (hpr x).1⟩
  have hadjπ : ∀ x y, (outerRelGraph G col w i).Adj x y → π x = π y := by
    intro x y hxy
    obtain ⟨-, t, ht, hxt, hyt, -⟩ := (outerRelGraph_adj_iff H hi).mp hxy
    exact Subtype.ext ((hπ x t ht hxt).symm.trans (hπ y t ht hyt))
  have hwalkπ : ∀ x y (p : (outerRelGraph G col w i).Walk x y), π x = π y := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadjπ _ _ h).trans ih
  let e₀ : (outerRelGraph G col w i).ConnectedComponent →
      {s : {v : V // col v = false} // (pointGraph G col).dist w s = i - 1} :=
    SimpleGraph.ConnectedComponent.lift π fun x y p _ => hwalkπ x y p
  have hline : ∀ (a b : {v : V // col v = false}), (pointGraph G col).Adj a b → ∀ m m' : V,
      G.Adj (a : V) m → G.Adj (b : V) m → G.Adj (a : V) m' → G.Adj (b : V) m' → m = m' :=
    fun a b hab m m' h1 h2 h3 h4 =>
      (exists_unique_common_line H col hab).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  have hcol : ∀ x y : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i}, x ≠ y →
      pr x = pr y → ¬ (outerRelGraph G col w i).Adj x y → ∀ mx : V,
      G.Adj ((x : {v : V // col v = false}) : V) mx → G.Adj (pr x : V) mx →
        G.Adj ((y : {v : V // col v = false}) : V) mx := by
    intro x y hxy hpp hn mx xmx smx
    by_contra hym
    apply hn
    refine (outerRelGraph_adj_iff H hi).mpr ⟨hxy, pr x, (hpr x).1, (hpr x).2,
      by rw [hpp]; exact (hpr y).2, fun m m' h1 h2 h3 h4 hmm => hym ?_⟩
    rw [← hmm, hline _ _ (hpr x).2 m mx h1 h2 xmx smx] at h3
    exact h3
  have hinj : Function.Injective e₀ := by
    intro C D
    induction C, D using SimpleGraph.ConnectedComponent.ind₂ with
    | h x y => ?_
    intro hxy
    have hpp : pr x = pr y := congrArg Subtype.val hxy
    apply SimpleGraph.ConnectedComponent.sound
    by_cases hxy' : x = y
    · rw [hxy']
    by_cases hadj : (outerRelGraph G col w i).Adj x y
    · exact hadj.reachable
    obtain ⟨mx, xmx, smx⟩ :=
      exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col _ _).mp (hpr x).2)
    have hymx := hcol x y hxy' hpp hadj mx xmx smx
    have hys : (pointGraph G col).Adj (y : {v : V // col v = false}) (pr x) := by
      rw [hpp]
      exact (hpr y).2
    obtain ⟨z, L, hz, hzs, hzL, hsL, hLm⟩ := exists_outward_point H hi (hpr x).1 mx
    have key : ∀ u : {x : {v : V // col v = false} // (pointGraph G col).dist w x = i},
        (pointGraph G col).Adj (u : {v : V // col v = false}) (pr x) →
        G.Adj ((u : {v : V // col v = false}) : V) mx →
          (outerRelGraph G col w i).Adj u ⟨z, hz⟩ := by
      intro u hus hum
      have hl : ∀ m m' : V, G.Adj ((u : {v : V // col v = false}) : V) m → G.Adj (pr x : V) m →
          G.Adj (z : V) m' → G.Adj (pr x : V) m' → m ≠ m' := fun m m' h1 h2 h3 h4 hmm =>
        hLm ((hline z (pr x) hzs m' L h3 h4 hzL hsL).symm.trans
          (hmm.symm.trans (hline _ _ hus m mx h1 h2 hum smx)))
      refine (outerRelGraph_adj_iff H hi).mpr ⟨fun hu => hl L L ?_ hsL hzL hsL rfl,
        pr x, (hpr x).1, hus, hzs, hl⟩
      rw [hu]
      exact hzL
    exact (key x (hpr x).2 xmx).reachable.trans (key y hys hymx).reachable.symm
  have hsurj : Function.Surjective e₀ := by
    intro s
    obtain ⟨z, -, hz, hzs, -⟩ := exists_outward_point H hi s.2 (s : V)
    exact ⟨(outerRelGraph G col w i).connectedComponentMk ⟨z, hz⟩,
      Subtype.ext (hπ ⟨z, hz⟩ s s.2 hzs).symm⟩
  refine ⟨Equiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun x => (hpr x).2, fun x y hxy hcc => ?_⟩
  have hpp : pr x = pr y := congrArg Subtype.val (congrArg e₀ hcc)
  have hys : (pointGraph G col).Adj (y : {v : V // col v = false}) (pr x) := by
    rw [hpp]
    exact (hpr y).2
  show ¬ (outerRelGraph G col w i).Adj x y ↔ ∃ m : V, ¬ IsOuterLine G col w i m ∧
    G.neighborFinset m = {(pr x : V), ((x : {v : V // col v = false}) : V),
      ((y : {v : V // col v = false}) : V)}
  constructor
  · intro hn
    obtain ⟨mx, xmx, smx⟩ :=
      exists_adj_adj_of_dist_eq_two H.conn ((point_adj_iff H.conn col _ _).mp (hpr x).2)
    have hymx := hcol x y hxy hpp hn mx xmx smx
    refine ⟨mx, fun h => ?_, neighborFinset_eq H smx xmx hymx
      (fun h => (hpr x).2.ne (Subtype.ext h).symm) (fun h => hys.ne (Subtype.ext h).symm)
      (fun h => hxy (Subtype.ext (Subtype.ext h)))⟩
    have h1 := h.2 (pr x) smx
    have h2 := (hpr x).1
    omega
  · rintro ⟨m, -, hN⟩ hadj
    have hmem : ∀ {u : V}, u ∈ ({(pr x : V), ((x : {v : V // col v = false}) : V),
        ((y : {v : V // col v = false}) : V)} : Finset V) → G.Adj u m := fun hu =>
      ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; exact hu)).symm
    obtain ⟨-, t, ht, hxt, -, hl⟩ := (outerRelGraph_adj_iff H hi).mp hadj
    rw [hπ x t ht hxt] at hl
    exact hl m m (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) (hmem (by simp)) rfl

end CFSG.Combinatorics.OuterLayer
