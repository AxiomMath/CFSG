module

public import CFSG.Combinatorics.AperiodicCentralInvolutionSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

section Defs

variable {V : Type*}

open scoped Classical in
noncomputable def sibling (G : SimpleGraph V) (col : G.Coloring Bool)
    (w t : {v : V // col v = false}) : {v : V // col v = false} :=
  if h : ∃ t', (pointGraph G col).dist w t' = 2 ∧ (pointGraph G col).Adj t t' then
    Classical.choose h else t

noncomputable def ptMap (G : SimpleGraph V) (col : G.Coloring Bool)
    (w x : {v : V // col v = false}) : {v : V // col v = false} :=
  if (pointGraph G col).dist w x = 3 then sigmaMap G col w x
  else if (pointGraph G col).dist w x = 2 then sibling G col w x else x

open scoped Classical in
noncomputable def lineMap (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (m : V) : V :=
  if h : ∃ m', col m' = true ∧ ∀ u : {v : V // col v = false}, G.Adj (u : V) m →
      G.Adj (ptMap G col w u : V) m' then Classical.choose h else m

noncomputable def incMap (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (v : V) : V :=
  if h : col v = false then (ptMap G col w ⟨v, h⟩ : V) else lineMap G col w v

end Defs

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
  (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)

include F in
theorem sibling_spec {t : {v : V // col v = false}} (ht : (pointGraph G col).dist w t = 2) :
    (pointGraph G col).dist w (sibling G col w t) = 2 ∧
      (pointGraph G col).Adj t (sibling G col w t) := by
  have hex : ∃ t', (pointGraph G col).dist w t' = 2 ∧ (pointGraph G col).Adj t t' := by
    obtain ⟨m, htm, -, ⟨a, t', hN, -, ht', ht't⟩, -⟩ :=
      inner_layer_lines F.moore col w (Or.inr rfl) t ht
    have ht'm : G.Adj (t' : V) m := by
      have h : (t' : V) ∈ G.neighborFinset m := by rw [hN]; simp
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm
    exact ⟨t', ht', (point_adj_iff F.moore.conn col _ _).mpr (dist_eq_two_of_adj_adj F.moore.conn
      col (fun h => ht't (Subtype.ext h.symm)) (t.2.trans t'.2.symm) htm ht'm)⟩
  rw [sibling, dite_eq_left hex]
  exact Classical.choose_spec hex

include F in
theorem eq_sibling {t t' : {v : V // col v = false}} (ht : (pointGraph G col).dist w t = 2)
    (ht' : (pointGraph G col).dist w t' = 2) (htt' : (pointGraph G col).Adj t t') :
    t' = sibling G col w t := by
  obtain ⟨m, htm, -, ⟨a, t₀, hN, ha, -, -⟩, hother⟩ :=
    inner_layer_lines F.moore col w (Or.inr rfl) t ht
  have key : ∀ u : {v : V // col v = false}, (pointGraph G col).dist w u = 2 →
      (pointGraph G col).Adj t u → u = t₀ := by
    intro u hu htu
    obtain ⟨n, htn, hun⟩ :=
      exists_adj_adj_of_dist_eq_two F.moore.conn ((point_adj_iff F.moore.conn col _ _).mp htu)
    have huN : (u : V) ∈ G.neighborFinset n := (SimpleGraph.mem_neighborFinset _ _ _).mpr hun.symm
    by_cases hnm : n = m
    · subst hnm
      rw [hN] at huN
      simp only [Finset.mem_insert, Finset.mem_singleton] at huN
      rcases huN with h | h | h
      · exact absurd (Subtype.ext h).symm htu.ne
      · rw [Subtype.ext h] at hu
        omega
      · exact Subtype.ext h
    · obtain ⟨b, b', hN', -, hb, hb'⟩ := hother n htn hnm
      rw [hN'] at huN
      simp only [Finset.mem_insert, Finset.mem_singleton] at huN
      rcases huN with h | h | h
      · exact absurd (Subtype.ext h).symm htu.ne
      · rw [Subtype.ext h] at hu
        omega
      · rw [Subtype.ext h] at hu
        omega
  rw [key t' ht' htt', key _ (sibling_spec F ht).1 (sibling_spec F ht).2]

include F in
theorem sibling_sibling {t : {v : V // col v = false}} (ht : (pointGraph G col).dist w t = 2) :
    sibling G col w (sibling G col w t) = t :=
  (eq_sibling F (sibling_spec F ht).1 ht (sibling_spec F ht).2.symm).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ptMap_of_three {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3) :
    ptMap G col w x = sigmaMap G col w x := by
  rw [ptMap, ite_eq_left hx]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ptMap_of_two {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 2) :
    ptMap G col w x = sibling G col w x := by
  rw [ptMap, ite_eq_right (by omega), ite_eq_left hx]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ptMap_of_le_one {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x ≤ 1) :
    ptMap G col w x = x := by
  rw [ptMap, ite_eq_right (by omega), ite_eq_right (by omega)]

include F in
theorem dist_le_three (x : {v : V // col v = false}) : (pointGraph G col).dist w x ≤ 3 := by
  rw [(point_dist F.moore.conn col w x).1]
  have := dist_le_six F.moore.cyc F.moore.conn col F.moore.deg F.moore.card (w : V) x
  omega

include F hr haper in
theorem dist_ptMap (x : {v : V // col v = false}) :
    (pointGraph G col).dist w (ptMap G col w x) = (pointGraph G col).dist w x := by
  have := dist_le_three F x
  by_cases h3 : (pointGraph G col).dist w x = 3
  · rw [ptMap_of_three h3, h3]
    exact sigmaMap_mem F hr haper h3
  · by_cases h2 : (pointGraph G col).dist w x = 2
    · rw [ptMap_of_two h2, h2]
      exact (sibling_spec F h2).1
    · rw [ptMap_of_le_one (x := x) (by omega)]

include F hr haper in
theorem ptMap_ptMap (x : {v : V // col v = false}) : ptMap G col w (ptMap G col w x) = x := by
  have := dist_le_three F x
  by_cases h3 : (pointGraph G col).dist w x = 3
  · rw [ptMap_of_three h3, ptMap_of_three (sigmaMap_mem F hr haper h3),
      sigmaMap_sigmaMap F hr haper h3]
  · by_cases h2 : (pointGraph G col).dist w x = 2
    · rw [ptMap_of_two h2, ptMap_of_two (sibling_spec F h2).1, sibling_sibling F h2]
    · rw [ptMap_of_le_one (x := x) (by omega), ptMap_of_le_one (x := x) (by omega)]

include F in
theorem line_eq_of_two {u v m m' : V} (huv : u ≠ v) (hu : col u = false) (hv : col v = false)
    (hum : G.Adj u m) (hvm : G.Adj v m) (hum' : G.Adj u m') (hvm' : G.Adj v m') : m = m' :=
  pred_unique F.moore.cyc F.moore.conn (k := 1) (by norm_num)
    (show G.dist u v = 1 + 1 from dist_eq_two_of_adj_adj F.moore.conn col huv (hu.trans hv.symm)
      hum hvm) hvm hvm' (SimpleGraph.dist_eq_one_iff_adj.mpr hum)
    (SimpleGraph.dist_eq_one_iff_adj.mpr hum')

include F hr haper in
theorem exists_line_image {m : V} (hm : col m = true) :
    ∃ m', col m' = true ∧ ∀ u : {v : V // col v = false}, G.Adj (u : V) m →
      G.Adj (ptMap G col w u : V) m' := by
  have hd := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  have hpt : ∀ {v : V}, G.Adj v m → col v = false := fun h =>
    col_eq_false_of_adj col hm h
  have hodd : ¬ Even (G.dist (w : V) m) := by
    intro he
    have h := (even_dist_iff F.moore.conn col (w : V) m).mp he
    rw [Bool.coe_iff_coe, w.2, hm] at h
    exact Bool.false_ne_true h
  have hle := dist_le_six F.moore.cyc F.moore.conn col F.moore.deg F.moore.card (w : V) m
  have hcases : G.dist (w : V) m = 1 ∨ G.dist (w : V) m = 3 ∨ G.dist (w : V) m = 5 := by
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨n, hn⟩ := hodd
    omega
  have hfix : ∀ u : {v : V // col v = false}, G.dist (w : V) u ≤ 2 → ptMap G col w u = u := by
    intro u hu
    refine ptMap_of_le_one ?_
    rw [(point_dist F.moore.conn col w u).1]
    omega
  rcases hcases with h1 | h3 | h5
  ·
    refine ⟨m, hm, fun u hu => ?_⟩
    rw [hfix u (by rcases dist_adj F.moore.conn col hu (w : V) with h | h <;> omega)]
    exact hu
  ·
    refine ⟨m, hm, fun u hu => ?_⟩
    obtain ⟨a, b, b', hN, ha, hb, hb', hbb'⟩ := nbr_structure F.moore col (k := 2) (by norm_num) h3
    have huN : (u : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr hu.symm
    rw [hN] at huN
    simp only [Finset.mem_insert, Finset.mem_singleton] at huN
    have hmem : ∀ {t : V}, t ∈ ({a, b, b'} : Finset V) → G.Adj t m := fun ht => by
      rw [← hN] at ht
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp ht).symm
    have hsib : ∀ {t t' : V}, t ∈ ({a, b, b'} : Finset V) → t' ∈ ({a, b, b'} : Finset V) →
        G.dist (w : V) t = 4 → G.dist (w : V) t' = 4 → t ≠ t' → (u : V) = t →
        G.Adj (ptMap G col w u : V) m := by
      intro t t' ht ht' h4 h4' htt' hut
      have hu2 : (pointGraph G col).dist w u = 2 := (hd w u 2).mpr (by rw [hut]; exact h4)
      let t'' : {v : V // col v = false} := ⟨t', hpt (hmem ht')⟩
      have hut'' : (pointGraph G col).Adj u t'' := by
        rw [hA]
        exact dist_eq_two_of_adj_adj F.moore.conn col (by rw [hut]; exact htt') (u.2.trans
          t''.2.symm) hu (hmem ht')
      rw [ptMap_of_two hu2, ← eq_sibling F hu2 ((hd w t'' 2).mpr h4') hut'']
      exact hmem ht'
    rcases huN with h | h | h
    · rw [hfix u (by rw [h]; omega)]
      exact hu
    · exact hsib (by simp) (by simp) hb hb' hbb' h
    · exact hsib (by simp) (by simp) hb' hb hbb'.symm h
  ·
    obtain ⟨a, b, b', hN, ha, hb, hb', hbb'⟩ := nbr_structure F.moore col (k := 4) (by norm_num) h5
    have hmem : ∀ {t : V}, t ∈ ({a, b, b'} : Finset V) → G.Adj t m := fun ht => by
      rw [← hN] at ht
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp ht).symm
    have hbm : G.Adj b m := hmem (by simp)
    have hb'm : G.Adj b' m := hmem (by simp)
    let x : {v : V // col v = false} := ⟨b, hpt hbm⟩
    let y : {v : V // col v = false} := ⟨b', hpt hb'm⟩
    have hx : (pointGraph G col).dist w x = 3 := (hd w x 3).mpr hb
    have hy : (pointGraph G col).dist w y = 3 := (hd w y 3).mpr hb'
    have hxy : (pointGraph G col).Adj x y := (hA x y).mpr (dist_eq_two_of_adj_adj F.moore.conn col
      hbb' (x.2.trans y.2.symm) hbm hb'm)
    have hNm := (F.data x hx y hy hxy).1 m hbm hb'm
    have hσx := sigmaMap_mem F hr haper hx
    have hσy := sigmaMap_mem F hr haper hy
    obtain ⟨m', -, σxm', σym', zm', z4, -⟩ :=
      F.edge hσx hσy ((adj_sigmaMap_iff F hr haper hx hy).mpr hxy)
    refine ⟨m', col_eq_true_of_adj col (sigmaMap G col w x).2 σxm', fun u hu => ?_⟩
    have huN : (u : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr hu.symm
    rw [hNm] at huN
    simp only [Finset.mem_insert, Finset.mem_singleton] at huN
    rcases huN with h | h | h
    · rw [Subtype.ext h, ptMap_of_three hx]
      exact σxm'
    · rw [Subtype.ext h, ptMap_of_three hy]
      exact σym'
    ·
      obtain ⟨_, -, -, -, -, z4x, -⟩ := F.edge hx hy hxy
      have hz2 : (pointGraph G col).dist w (z x y) = 2 := (hd w _ 2).mpr z4x
      rw [Subtype.ext h, ptMap_of_two hz2, ← eq_sibling F hz2 ((hd w _ 2).mpr z4)
        (adj_third_sigmaMap F hr haper hx hy hxy)]
      exact zm'

include F hr haper in
theorem lineMap_spec {m : V} (hm : col m = true) :
    col (lineMap G col w m) = true ∧ ∀ u : {v : V // col v = false}, G.Adj (u : V) m →
      G.Adj (ptMap G col w u : V) (lineMap G col w m) := by
  have hex := exists_line_image F hr haper hm
  rw [lineMap, dite_eq_left hex]
  exact Classical.choose_spec hex

include F hr haper in
theorem lineMap_lineMap {m : V} (hm : col m = true) :
    lineMap G col w (lineMap G col w m) = m := by
  obtain ⟨hm₁, hsp₁⟩ := lineMap_spec F hr haper hm
  obtain ⟨-, hsp₂⟩ := lineMap_spec F hr haper hm₁
  have hcard : (G.neighborFinset m).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, F.moore.deg]
  obtain ⟨a, b, _, hab, -, -, hN⟩ := Finset.card_eq_three.mp hcard
  have ham : G.Adj a m := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have hbm : G.Adj b m := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have hpt : ∀ {v : V}, G.Adj v m → col v = false := fun h => col_eq_false_of_adj col hm h
  have himg : ∀ {v : V} (hv : G.Adj v m), G.Adj v (lineMap G col w (lineMap G col w m)) := by
    intro v hv
    have := hsp₂ _ (hsp₁ ⟨v, hpt hv⟩ hv)
    rwa [ptMap_ptMap F hr haper] at this
  exact (line_eq_of_two F hab (hpt ham) (hpt hbm) ham hbm (himg ham) (himg hbm)).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem incMap_point (x : {v : V // col v = false}) :
    incMap G col w (x : V) = (ptMap G col w x : V) := by
  rw [incMap, dite_eq_left x.2]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem incMap_line {m : V} (hm : col m = true) : incMap G col w m = lineMap G col w m := by
  rw [incMap, dite_eq_right (by simp [hm])]

include F hr haper in
theorem col_incMap (v : V) : col (incMap G col w v) = col v := by
  rcases Bool.eq_false_or_eq_true (col v) with hv | hv
  · rw [incMap_line hv, (lineMap_spec F hr haper hv).1, hv]
  · rw [show v = ((⟨v, hv⟩ : {v : V // col v = false}) : V) from rfl, incMap_point]
    exact (ptMap G col w ⟨v, hv⟩).2.trans hv.symm

include F hr haper in
theorem incMap_incMap (v : V) : incMap G col w (incMap G col w v) = v := by
  rcases Bool.eq_false_or_eq_true (col v) with hv | hv
  · rw [incMap_line hv, incMap_line (lineMap_spec F hr haper hv).1, lineMap_lineMap F hr haper hv]
  · rw [show v = ((⟨v, hv⟩ : {v : V // col v = false}) : V) from rfl, incMap_point, incMap_point,
      ptMap_ptMap F hr haper]

include F hr haper in
theorem adj_incMap_of_adj {a b : V} (hab : G.Adj a b) :
    G.Adj (incMap G col w a) (incMap G col w b) := by
  have key : ∀ {a b : V}, G.Adj a b → col a = false →
      G.Adj (incMap G col w a) (incMap G col w b) := by
    intro a b hab ha
    have hb : col b = true := col_eq_true_of_adj col ha hab
    rw [show a = ((⟨a, ha⟩ : {v : V // col v = false}) : V) from rfl, incMap_point,
      incMap_line hb]
    exact (lineMap_spec F hr haper hb).2 ⟨a, ha⟩ hab
  rcases Bool.eq_false_or_eq_true (col a) with ha | ha
  · exact (key hab.symm (col_eq_false_of_adj col ha hab.symm)).symm
  · exact key hab ha

include F hr haper in
theorem adj_incMap_iff (a b : V) :
    G.Adj (incMap G col w a) (incMap G col w b) ↔ G.Adj a b := by
  refine ⟨fun h => ?_, adj_incMap_of_adj F hr haper⟩
  have := adj_incMap_of_adj F hr haper h
  rwa [incMap_incMap F hr haper, incMap_incMap F hr haper] at this

end CFSG.Combinatorics.AperiodicOppositeComponents
