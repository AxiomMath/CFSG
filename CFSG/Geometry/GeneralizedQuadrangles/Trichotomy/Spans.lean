module

public import CFSG.Geometry.GeneralizedQuadrangles.LinearSpace

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section SpanOrLine

variable {Γ : SimpleGraph V}

@[expose] noncomputable def spanOrLine (hP : IsGeneralizedPolygon Γ 4) (x y : V) : Set V :=
  if Γ.dist x y = 4 then spanSet Γ x y
  else if h : Γ.dist x y = 2 then Γ.neighborSet (commonNeighbor hP h) else ∅

theorem spanOrLine_of_dist_eq_four (hP : IsGeneralizedPolygon Γ 4) {x y : V}
    (h : Γ.dist x y = 4) : spanOrLine hP x y = spanSet Γ x y := by
  classical
  rw [spanOrLine, if_pos h]

theorem spanOrLine_of_dist_eq_two (hP : IsGeneralizedPolygon Γ 4) {x y : V}
    (h : Γ.dist x y = 2) :
    spanOrLine hP x y = Γ.neighborSet (commonNeighbor hP h) := by
  classical
  rw [spanOrLine, if_neg (by rw [h]; norm_num), dif_pos h]

@[simp] theorem mem_spanOrLine_of_dist_eq_four (hP : IsGeneralizedPolygon Γ 4) {x y z : V}
    (h : Γ.dist x y = 4) : z ∈ spanOrLine hP x y ↔ z ∈ spanSet Γ x y := by
  rw [spanOrLine_of_dist_eq_four hP h]

end SpanOrLine

section BlockThrough

variable {Γ : SimpleGraph V}

@[expose] def blockThrough (Γ : SimpleGraph V) (y : V) (T : Set V) : Set V :=
  {u | ∃ W : V, Γ.Adj y W ∧ (∃ t ∈ T, Γ.Adj W t) ∧ Γ.Adj W u}

@[simp] theorem mem_blockThrough {y u : V} {T : Set V} :
    u ∈ blockThrough Γ y T ↔
      ∃ W : V, Γ.Adj y W ∧ (∃ t ∈ T, Γ.Adj W t) ∧ Γ.Adj W u := Iff.rfl

theorem neighborSet_subset_blockThrough {y W : V} {T : Set V}
    (hyW : Γ.Adj y W) (hWT : ∃ t ∈ T, Γ.Adj W t) :
    Γ.neighborSet W ⊆ blockThrough Γ y T := by
  intro u hu
  exact ⟨W, hyW, hWT, hu⟩

@[expose] def spanBlock (Γ : SimpleGraph V) (y a b : V) : Set V :=
  blockThrough Γ y (spanSet Γ a b)

end BlockThrough

section SpanUnion

variable {Γ : SimpleGraph V}

@[expose] noncomputable def spanUnion (hP : IsGeneralizedPolygon Γ 4) (L M : V) : Set V :=
  {u | ∃ x y : V, Γ.Adj L x ∧ Γ.Adj M y ∧ u ∈ spanOrLine hP x y}

@[simp] theorem mem_spanUnion (hP : IsGeneralizedPolygon Γ 4) {L M u : V} :
    u ∈ spanUnion hP L M ↔
      ∃ x y : V, Γ.Adj L x ∧ Γ.Adj M y ∧ u ∈ spanOrLine hP x y := Iff.rfl

end SpanUnion

section Colours

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem color_eq_of_adj_adj {c : Γ.Coloring (Fin 2)} {W a b : V}
    (ha : Γ.Adj W a) (hb : Γ.Adj W b) : c a = c b := by
  have h1 : c a ≠ c W := (c.valid ha).symm
  have h2 : c b ≠ c W := (c.valid hb).symm
  have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases hfin (c W) with hW | hW <;> rcases hfin (c a) with ha' | ha' <;>
    rcases hfin (c b) with hb' | hb' <;> simp_all

private theorem color_eq_of_mem_span_of_adj_left
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L x y z : V} (hL : c L = 1) (hLx : Γ.Adj L x) (hxy : Γ.dist x y = 4)
    (hz : z ∈ spanSet Γ x y) : c z = c x := by
  exact color_eq_of_mem_span hP hT c hxy hz

private theorem dist_eq_three_of_span
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L x y z : V} (hL : c L = 1) (hLx : Γ.Adj L x) (hzL : ¬ Γ.Adj L z)
    (hxy : Γ.dist x y = 4) (hz : z ∈ spanSet Γ x y) : Γ.dist z L = 3 := by
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLx
  have hcz : c z = c x := color_eq_of_mem_span_of_adj_left hP hT c hL hLx hxy hz
  exact dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hzL h.symm)
    (by rw [hcz, hx0, hL]; decide)

private theorem dist_eq_three_of_adj_adj
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L x W z : V} (hL : c L = 1) (hLx : Γ.Adj L x) (hxW : Γ.Adj W x)
    (hzW : Γ.Adj W z) (hzL : ¬ Γ.Adj L z) : Γ.dist z L = 3 := by
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLx
  have hcz : c z = c x := color_eq_of_adj_adj (Γ := Γ) hzW hxW
  exact dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hzL h.symm)
    (by rw [hcz, hx0, hL]; decide)

theorem not_adj_of_dist_eq_four_of_adj_right
    (hP : IsGeneralizedPolygon Γ 4) {L M y : V} (hLM : Γ.dist L M = 4)
    (hyM : Γ.Adj M y) : ¬ Γ.Adj L y := by
  intro hLy
  have hLM2 : Γ.dist L M = 2 := by
    refine dist_eq_two_of_adj_of_adj_of_ne hP hLy ?_ ?_
    · exact hyM.symm
    · intro hLM_eq
      rw [hLM_eq, SimpleGraph.dist_self] at hLM
      omega
  omega

private theorem dist_eq_three_of_adj_right
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L M y : V} (hL : c L = 1) (hM : c M = 1) (hyM : Γ.Adj M y)
    (hLM : Γ.dist L M = 4) : Γ.dist y L = 3 := by
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hyM
  exact dist_eq_three_of_not_adj_of_color_ne hP c
    (fun h => (not_adj_of_dist_eq_four_of_adj_right (L := L) (M := M) (y := y)
      hP hLM hyM) h.symm) (by rw [hy0, hL]; decide)

theorem not_adj_of_dist_eq_four_of_adj_left
    (hP : IsGeneralizedPolygon Γ 4) {L M x : V} (hLM : Γ.dist L M = 4)
    (hxL : Γ.Adj L x) : ¬ Γ.Adj M x := by
  intro hMx
  have hLM2 : Γ.dist L M = 2 := by
    refine dist_eq_two_of_adj_of_adj_of_ne hP hxL ?_ ?_
    · exact hMx.symm
    · intro hLM_eq
      rw [hLM_eq, SimpleGraph.dist_self] at hLM
      omega
  omega

private theorem eq_of_adj_right_of_dist_eq_two
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {L M w y y' : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hwL : Γ.Adj L w) (hyM : Γ.Adj M y) (hy'M : Γ.Adj M y')
    (hwy : Γ.dist w y = 2) (hwy' : Γ.dist w y' = 2) : y = y' := by
  have hw0 : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hL hwL
  have hwM : Γ.dist w M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c
      (fun h => (not_adj_of_dist_eq_four_of_adj_left (L := L) (M := M) (x := w) hP hLM hwL)
        h.symm) (by rw [hw0, hM]; decide)
  exact (existsUnique_proj hP hwM).unique ⟨hyM, hwy⟩ ⟨hy'M, hwy'⟩

private theorem eq_proj_of_mem_span (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {L x y z : V} (hy3 : Γ.dist y L = 3) (hz3 : Γ.dist z L = 3)
    (hLx : Γ.Adj L x) (hxy : Γ.dist x y = 4) (hz : z ∈ spanSet Γ x y) :
    proj hP hz3 = proj hP hy3 := by
  have hLw : Γ.Adj L (proj hP hy3) := proj_adj hP hy3
  have hwy : Γ.dist y (proj hP hy3) = 2 := proj_dist hP hy3
  have hwx : Γ.dist x (proj hP hy3) = 2 := by
    rw [SimpleGraph.dist_comm]
    refine dist_eq_two_of_adj_of_adj_of_ne hP (x := proj hP hy3) (y := x) (L := L)
      hLw.symm hLx ?_
    intro hEq
    rw [hEq, SimpleGraph.dist_comm] at hwy
    omega
  have hwtrace : proj hP hy3 ∈ traceSet Γ x y := ⟨hwx, hwy⟩
  have hzw : Γ.dist z (proj hP hy3) = 2 :=
    dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hz hwtrace
  exact (eq_proj hP hz3 hLw hzw).symm

private theorem eq_proj_of_adj_adj (hP : IsGeneralizedPolygon Γ 4)
    {L x W z : V} (hz3 : Γ.dist z L = 3) (hLx : Γ.Adj L x)
    (hxW : Γ.Adj W x) (hzW : Γ.Adj W z) (hzx : z ≠ x) :
    proj hP hz3 = x := by
  have hzx2 : Γ.dist z x = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := z) (y := x) (L := W) hzW.symm hxW hzx
  exact (eq_proj hP hz3 hLx hzx2).symm

private theorem spanSet_inter_spanSet_subset
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L M x x' y y' : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hLx' : Γ.Adj L x') (hMy : Γ.Adj M y) (hMy' : Γ.Adj M y')
    (hxy : Γ.dist x y = 4) (hx'y' : Γ.dist x' y' = 4)
    (hne : (x, y) ≠ (x', y')) :
    spanSet Γ x y ∩ spanSet Γ x' y' ⊆ Γ.neighborSet L ∪ Γ.neighborSet M := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  by_cases hzL : z ∈ Γ.neighborSet L
  · exact Or.inl hzL
  by_cases hzM : z ∈ Γ.neighborSet M
  · exact Or.inr hzM
  exfalso
  have hzL' : ¬ Γ.Adj L z := hzL
  have hzM' : ¬ Γ.Adj M z := hzM
  have hy3 : Γ.dist y L = 3 := dist_eq_three_of_adj_right hP c hL hM hMy hLM
  have hy'3 : Γ.dist y' L = 3 := dist_eq_three_of_adj_right hP c hL hM hMy' hLM
  have hz3 : Γ.dist z L = 3 :=
    dist_eq_three_of_span hP hT c hL hLx hzL' hxy hz1
  by_cases hyy : y = y'
  · subst hyy
    have hxne : x ≠ x' := by
      rintro rfl
      exact hne rfl
    have hzy : z ≠ y := fun h => hzM' (h ▸ hMy)
    have hsp1 := span_eq_of_mem hP hT hxy hz1 (right_mem_spanSet hxy) hzy
    have hsp2 := span_eq_of_mem hP hT hx'y' hz2 (right_mem_spanSet hx'y') hzy
    have hspan : spanSet Γ x y = spanSet Γ x' y := by
      rw [← hsp1.2.1, ← hsp2.2.1]
    have hxmem : x ∈ spanSet Γ x y := left_mem_spanSet hxy
    have hx'mem : x' ∈ spanSet Γ x y := by
      rw [hspan]
      exact left_mem_spanSet hx'y'
    have hdist4 : Γ.dist x x' = 4 :=
      dist_eq_four_of_mem_span hP hT hxy hxmem hx'mem hxne
    have hdist2 : Γ.dist x x' = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := x) (y := x') (L := L)
        hLx.symm hLx' hxne
    omega
  · have hwx : proj hP hz3 = proj hP hy3 :=
      eq_proj_of_mem_span hP hT hy3 hz3 hLx hxy hz1
    have hwx' : proj hP hz3 = proj hP hy'3 :=
      eq_proj_of_mem_span hP hT hy'3 hz3 hLx' hx'y' hz2
    have hw : proj hP hy3 = proj hP hy'3 := hwx.symm.trans hwx'
    have hwL : Γ.Adj L (proj hP hy3) := proj_adj hP hy3
    have h1 : Γ.dist (proj hP hy3) y = 2 := by
      rw [SimpleGraph.dist_comm]
      exact proj_dist hP hy3
    have h2 : Γ.dist (proj hP hy3) y' = 2 := by
      have h := proj_dist hP hy'3
      rw [← hw, SimpleGraph.dist_comm] at h
      exact h
    exact hyy (eq_of_adj_right_of_dist_eq_two hP c hL hM hLM hwL hMy hMy' h1 h2)

private theorem neighborSet_commonNeighbor_inter_spanSet_subset
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L M x x' y y' : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hLx' : Γ.Adj L x') (hMy : Γ.Adj M y) (hMy' : Γ.Adj M y')
    (h2 : Γ.dist x y = 2) (hx'y' : Γ.dist x' y' = 4)
    (hne : (x, y) ≠ (x', y')) :
    Γ.neighborSet (commonNeighbor hP h2) ∩ spanSet Γ x' y' ⊆
      Γ.neighborSet L ∪ Γ.neighborSet M := by
  intro z hz
  obtain ⟨hzV, hzS⟩ := hz
  by_cases hzL : z ∈ Γ.neighborSet L
  · exact Or.inl hzL
  by_cases hzM : z ∈ Γ.neighborSet M
  · exact Or.inr hzM
  exfalso
  have hzL' : ¬ Γ.Adj L z := hzL
  have hzM' : ¬ Γ.Adj M z := hzM
  have hxV : Γ.Adj x (commonNeighbor hP h2) := commonNeighbor_adj_left hP h2
  have hyV : Γ.Adj y (commonNeighbor hP h2) := commonNeighbor_adj_right hP h2
  have hz3 : Γ.dist z L = 3 :=
    dist_eq_three_of_span hP hT c hL hLx' hzL' hx'y' hzS
  have hzx : proj hP hz3 = x :=
    eq_proj_of_adj_adj hP hz3 hLx hxV.symm hzV (by rintro rfl; exact hzL' hLx)
  have hy'3 : Γ.dist y' L = 3 := dist_eq_three_of_adj_right hP c hL hM hMy' hLM
  have hw : proj hP hz3 = proj hP hy'3 :=
    eq_proj_of_mem_span hP hT (x := x') (y := y') hy'3 hz3 hLx' hx'y' hzS
  have hproj : proj hP hy'3 = x := hw.symm.trans hzx
  have h1 : Γ.dist x y = 2 := h2
  have h2' : Γ.dist x y' = 2 := by
    rw [← hproj, SimpleGraph.dist_comm]
    exact proj_dist hP hy'3
  have hyy : y = y' :=
    eq_of_adj_right_of_dist_eq_two hP c hL hM hLM hLx hMy hMy' h1 h2'
  subst hyy
  have hzy : z ≠ y := fun h => hzM' (h ▸ hMy)
  have hdist4 : Γ.dist z y = 4 :=
    dist_eq_four_of_mem_span hP hT hx'y' hzS (right_mem_spanSet hx'y') hzy
  have hdist2 : Γ.dist z y = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := z) (y := y)
      (L := commonNeighbor hP h2) hzV.symm hyV.symm hzy
  omega

private theorem neighborSet_inter_neighborSet_subset
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L M x x' y y' : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hLx' : Γ.Adj L x') (hMy : Γ.Adj M y) (hMy' : Γ.Adj M y')
    (h2 : Γ.dist x y = 2) (h2' : Γ.dist x' y' = 2)
    (hne : (x, y) ≠ (x', y')) :
    Γ.neighborSet (commonNeighbor hP h2) ∩
      Γ.neighborSet (commonNeighbor hP h2') ⊆ Γ.neighborSet L ∪ Γ.neighborSet M := by
  intro z hz
  obtain ⟨hzV, hzV'⟩ := hz
  by_cases hzL : z ∈ Γ.neighborSet L
  · exact Or.inl hzL
  by_cases hzM : z ∈ Γ.neighborSet M
  · exact Or.inr hzM
  exfalso
  have hzL' : ¬ Γ.Adj L z := hzL
  have hzM' : ¬ Γ.Adj M z := hzM
  have hxV : Γ.Adj x (commonNeighbor hP h2) := commonNeighbor_adj_left hP h2
  have hyV : Γ.Adj y (commonNeighbor hP h2) := commonNeighbor_adj_right hP h2
  have hx'V' : Γ.Adj x' (commonNeighbor hP h2') := commonNeighbor_adj_left hP h2'
  have hy'V' : Γ.Adj y' (commonNeighbor hP h2') := commonNeighbor_adj_right hP h2'
  have hz3 : Γ.dist z L = 3 :=
    dist_eq_three_of_adj_adj hP c hL hLx hxV.symm hzV hzL'
  have hz3' : Γ.dist z L = 3 :=
    dist_eq_three_of_adj_adj hP c hL hLx' hx'V'.symm hzV' hzL'
  have hzx : proj hP hz3 = x :=
    eq_proj_of_adj_adj hP hz3 hLx hxV.symm hzV (by rintro rfl; exact hzL' hLx)
  have hzx' : proj hP hz3' = x' :=
    eq_proj_of_adj_adj hP hz3' hLx' hx'V'.symm hzV' (by rintro rfl; exact hzL' hLx')
  have hxx : x = x' := by
    rw [← hzx, ← hzx']
  have hzM3 : Γ.dist z M = 3 :=
    dist_eq_three_of_adj_adj hP c hM hMy hyV.symm hzV hzM'
  have hzM3' : Γ.dist z M = 3 :=
    dist_eq_three_of_adj_adj hP c hM hMy' hy'V'.symm hzV' hzM'
  have hzy : proj hP hzM3 = y :=
    eq_proj_of_adj_adj hP hzM3 hMy hyV.symm hzV (by rintro rfl; exact hzM' hMy)
  have hzy' : proj hP hzM3' = y' :=
    eq_proj_of_adj_adj hP hzM3' hMy' hy'V'.symm hzV' (by rintro rfl; exact hzM' hMy')
  have hyy : y = y' := by
    rw [← hzy, ← hzy']
  exact hne (by rw [hxx, hyy])

end Colours

section StepOne

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem spanOrLine_inter_subset
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L M x x' y y' : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hLx' : Γ.Adj L x') (hMy : Γ.Adj M y) (hMy' : Γ.Adj M y')
    (hne : (x, y) ≠ (x', y')) :
    spanOrLine hP x y ∩ spanOrLine hP x' y' ⊆
      Γ.neighborSet L ∪ Γ.neighborSet M := by
  intro z hz
  by_cases h4 : Γ.dist x y = 4
  · rw [spanOrLine_of_dist_eq_four hP h4] at hz
    by_cases h4' : Γ.dist x' y' = 4
    · rw [spanOrLine_of_dist_eq_four hP h4'] at hz
      exact spanSet_inter_spanSet_subset hP hT c hL hM hLM
        hLx hLx' hMy hMy' h4 h4' hne hz
    · by_cases h2' : Γ.dist x' y' = 2
      · rw [spanOrLine_of_dist_eq_two hP h2'] at hz
        have hz' : z ∈ Γ.neighborSet (commonNeighbor hP h2') ∩ spanSet Γ x y :=
          ⟨hz.2, hz.1⟩
        have hne' : (x', y') ≠ (x, y) := fun h => hne h.symm
        exact neighborSet_commonNeighbor_inter_spanSet_subset hP hT c hL hM hLM
          hLx' hLx hMy' hMy h2' h4 hne' hz'
      · have hnil : spanOrLine hP x' y' = ∅ := by
          rw [spanOrLine, if_neg h4', dif_neg h2']
        simp [hnil] at hz
  · by_cases h2 : Γ.dist x y = 2
    · rw [spanOrLine_of_dist_eq_two hP h2] at hz
      by_cases h4' : Γ.dist x' y' = 4
      · rw [spanOrLine_of_dist_eq_four hP h4'] at hz
        exact neighborSet_commonNeighbor_inter_spanSet_subset hP hT c hL hM hLM
          hLx hLx' hMy hMy' h2 h4' hne hz
      · by_cases h2' : Γ.dist x' y' = 2
        · rw [spanOrLine_of_dist_eq_two hP h2'] at hz
          exact neighborSet_inter_neighborSet_subset hP c hL hM hLM
            hLx hLx' hMy hMy' h2 h2' hne hz
        · have hnil : spanOrLine hP x' y' = ∅ := by
            rw [spanOrLine, if_neg h4', dif_neg h2']
          simp [hnil] at hz
    · have hnil : spanOrLine hP x y = ∅ := by
        rw [spanOrLine, if_neg h4, dif_neg h2]
      simp [hnil] at hz

end StepOne

section BlockProjection

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem mem_spanSet_of_mem_block_projection
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {y : V} (hH : HasPropertyH Γ y) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {L M N W x a b yb z1 z2 : V}
    (hL : c L = 1) (hM : c M = 1) (hN : c N = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hLb : Γ.Adj L b) (hbx : b ≠ x)
    (hxV : Γ.Adj x W) (hVy : Γ.Adj W y) (hz1V : Γ.Adj W z1) (hz1y : z1 ≠ y)
    (hMy : Γ.Adj M y) (hMyb : Γ.Adj M yb) (hbyb : Γ.dist b yb = 2)
    (hNy : Γ.Adj N y) (hNyM : N ≠ M)
    (hNT : ∃ t ∈ spanSet Γ z1 z2, Γ.Adj N t)
    (hNa : Γ.Adj N a) (hba : Γ.dist b a = 2) (haz : a ≠ y)
    (hayb : Γ.dist a yb = 4) (hz2M : Γ.Adj M z2) (hz2y : z2 ≠ y)
    (hz1z2 : Γ.dist z1 z2 = 4) :
    x ∈ spanSet Γ a yb := by
  classical
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLx
  have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLb
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMy
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hN hNa
  have hyb0 : c yb = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMyb
  have hV1 : c W = 1 := by
    have hne := c.valid hxV
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c W) with hV0 | hV1
    · exact absurd (hx0.trans hV0.symm) hne
    · exact hV1
  have hya : Γ.dist y a = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := a) (L := N)
      hNy.symm hNa haz.symm
  have hxy_ne : x ≠ y := by
    rintro rfl
    exact (not_adj_of_dist_eq_four_of_adj_right (L := L) (M := M) hP hLM hMy)
      hLx
  have hxy2 : Γ.dist x y = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := x) (y := y) (L := W)
      hxV hVy hxy_ne
  have hyyb_ne : y ≠ yb := by
    intro hyeq
    have hby : Γ.dist b y = 2 := hyeq ▸ hbyb
    have hyL3 : Γ.dist y L = 3 := dist_eq_three_of_adj_right hP c hL hM hMy hLM
    have hby' : Γ.dist y b = 2 := by rw [SimpleGraph.dist_comm]; exact hby
    have hxy' : Γ.dist y x = 2 := by rw [SimpleGraph.dist_comm]; exact hxy2
    have hbproj : b = proj hP hyL3 := eq_proj hP hyL3 hLb hby'
    have hxproj : x = proj hP hyL3 := eq_proj hP hyL3 hLx hxy'
    exact hbx (hbproj.trans hxproj.symm)
  have hyyb : Γ.dist y yb = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := yb) (L := M)
      hMy.symm hMyb hyyb_ne
  have hyz1 : Γ.dist y z1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := z1) (L := W)
      hVy.symm hz1V hz1y.symm
  have hyz2 : Γ.dist y z2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := z2) (L := M)
      hMy.symm hz2M hz2y.symm
  have hNmem : N ∈ linesThrough Γ y (spanSet Γ z1 z2) ∩
      linesThrough Γ y (spanSet Γ a yb) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨hNy.symm, hNT⟩
    · rw [mem_linesThrough]
      refine ⟨hNy.symm, a, left_mem_spanSet hayb, hNa⟩
  have hMmem : M ∈ linesThrough Γ y (spanSet Γ z1 z2) ∩
      linesThrough Γ y (spanSet Γ a yb) := by
    constructor
    · rw [mem_linesThrough]
      exact ⟨hMy.symm, z2, right_mem_spanSet hz1z2, hz2M⟩
    · rw [mem_linesThrough]
      exact ⟨hMy.symm, yb, right_mem_spanSet hayb, hMyb⟩
  have hNM : N ≠ M := hNyM
  have hlines : linesThrough Γ y (spanSet Γ z1 z2) =
      linesThrough Γ y (spanSet Γ a yb) :=
    linesThrough_spanSet_eq_of_two_lines hP hT c hy0 hH hp
      hyz1 hyz2 hya hyyb hz1z2 hayb hNmem hMmem hNM
  have hVmem : W ∈ linesThrough Γ y (spanSet Γ z1 z2) := by
    rw [mem_linesThrough]
    exact ⟨hVy.symm, z1, left_mem_spanSet hz1z2, hz1V⟩
  have hVmem' : W ∈ linesThrough Γ y (spanSet Γ a yb) := by
    rw [hlines] at hVmem
    exact hVmem
  obtain ⟨sv, hsvS, hVsv⟩ := hVmem'.2
  have hbtrace : b ∈ traceSet Γ a yb :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hba, by rw [SimpleGraph.dist_comm]; exact hbyb⟩
  have hbs : Γ.dist sv b = 2 :=
    dist_eq_two_of_mem_span_of_mem_trace hP hT hayb hsvS hbtrace
  have hbS : b ∉ spanSet Γ a yb :=
    not_mem_spanSet_of_mem_traceSet hP hT hayb hbtrace
  have hbV : ¬ Γ.Adj W b := by
    intro hVb
    have hxb2 : Γ.dist x b = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := x) (y := b) (L := L)
        hLx.symm hLb hbx.symm
    have hVL : W = L :=
      (existsUnique_commonNeighbor hP hxb2).unique
        ⟨hxV, hVb.symm⟩ ⟨hLx.symm, hLb.symm⟩
    exact (not_adj_of_dist_eq_four_of_adj_right (L := L) (M := M) hP hLM hMy)
      (hVL ▸ hVy)
  have hbV3 : Γ.dist b W = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hbV h.symm)
      (by rw [hb0, hV1]; decide)
  have hxb2 : Γ.dist b x = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := b) (y := x) (L := L)
      hLb.symm hLx hbx
  have hxs : x = sv :=
    (existsUnique_proj hP hbV3).unique ⟨hxV.symm, hxb2⟩
      ⟨hVsv, by rw [SimpleGraph.dist_comm]; exact hbs⟩
  rw [hxs]
  exact hsvS

end BlockProjection

end CFSG.Geometry.GeneralizedQuadrangles
