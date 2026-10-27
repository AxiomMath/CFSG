module

public import CFSG.Geometry.GeneralizedQuadrangles.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Symmetry

variable {Γ : SimpleGraph V}

theorem traceSet_comm (x y : V) : traceSet Γ x y = traceSet Γ y x := by
  ext w
  simp only [mem_traceSet]
  exact and_comm

theorem spanSet_comm (x y : V) : spanSet Γ x y = spanSet Γ y x := by
  unfold spanSet
  rw [traceSet_comm]

theorem clSet_comm (x y : V) : clSet Γ x y = clSet Γ y x := by
  unfold clSet
  rw [spanSet_comm]

end Symmetry

section LinesThrough

variable {Γ : SimpleGraph V}

@[expose] def linesThrough (Γ : SimpleGraph V) (u : V) (T : Set V) : Set V :=
  {L | Γ.Adj u L ∧ ∃ w ∈ T, Γ.Adj L w}

@[simp] theorem mem_linesThrough {u : V} {T : Set V} {L : V} :
    L ∈ linesThrough Γ u T ↔ Γ.Adj u L ∧ ∃ w ∈ T, Γ.Adj L w := Iff.rfl

end LinesThrough

section NeLine

variable {Γ : SimpleGraph V}

theorem dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor
    (hP : IsGeneralizedPolygon Γ 4) {u x y : V}
    (hux : Γ.dist u x = 2) (huy : Γ.dist u y = 2)
    (hne : commonNeighbor hP hux ≠ commonNeighbor hP huy) : Γ.dist x y = 4 := by
  classical
  obtain ⟨c⟩ := hP.isBipartite
  have hxc : c x = c u :=
    ((hP.eq_iff_even_dist c u x).2 (by rw [hux]; norm_num)).symm
  have hyc : c y = c u :=
    ((hP.eq_iff_even_dist c u y).2 (by rw [huy]; norm_num)).symm
  have heven : Even (Γ.dist x y) := (hP.eq_iff_even_dist c x y).1 (hxc.trans hyc.symm)
  have hle : Γ.dist x y ≤ 4 := hP.dist_le (by norm_num) x y
  have hne0 : Γ.dist x y ≠ 0 := by
    intro h0
    have hxy : x = y := (hP.connected.dist_eq_zero_iff).mp h0
    subst hxy
    exact hne (by rw [Subsingleton.elim hux huy])
  by_contra hne4
  have hd2 : Γ.dist x y = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨v, hv, -⟩ :=
    existsUnique_commonNeighbor_of_pairwise_dist_two hP hux huy hd2
  have hvx : v = commonNeighbor hP hux :=
    (existsUnique_commonNeighbor hP hux).unique ⟨hv.1, hv.2.1⟩
      ⟨commonNeighbor_adj_left hP hux, commonNeighbor_adj_right hP hux⟩
  have hvy : v = commonNeighbor hP huy :=
    (existsUnique_commonNeighbor hP huy).unique ⟨hv.1, hv.2.2⟩
      ⟨commonNeighbor_adj_left hP huy, commonNeighbor_adj_right hP huy⟩
  exact hne (hvx.symm.trans hvy)

end NeLine

section ClosureViaLines

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem mem_clSet_iff_line_meets_span
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {u x y z : V}
    (hux : Γ.dist u x = 2) (huy : Γ.dist u y = 2) (huz : Γ.dist u z = 2)
    (hxy : Γ.dist x y = 4) (hxz : Γ.dist x z = 4) (hyz : Γ.dist y z = 4) :
    z ∈ clSet Γ x y ↔ ∃ w ∈ spanSet Γ x y, Γ.Adj (commonNeighbor hP huz) w := by
  classical
  constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := hz
    by_cases hwu : w = u
    · exact ⟨w, hw, by rw [hwu]; exact (commonNeighbor_adj_left hP huz).symm⟩
    obtain ⟨c⟩ := hP.isBipartite
    have hcz : c z = c u :=
      ((hP.eq_iff_even_dist c u z).2 (by rw [huz]; norm_num)).symm
    have hcu : c u = c x :=
      (hP.eq_iff_even_dist c u x).2 (by rw [hux]; norm_num)
    have hcw : c w = c x := color_eq_of_mem_span hP hT c hxy hw
    have hczw : c z = c w := hcz.trans (hcu.trans hcw.symm)
    have heven : Even (Γ.dist z w) := (hP.eq_iff_even_dist c z w).1 hczw
    have hzero_or_two : Γ.dist z w = 0 ∨ Γ.dist z w = 2 := by
      obtain ⟨k, hk⟩ := heven
      omega
    rcases hzero_or_two with h0 | h2
    · have hwz : w = z := ((hP.connected.dist_eq_zero_iff).mp h0).symm
      exact ⟨w, hw, by rw [hwz]; exact (commonNeighbor_adj_right hP huz).symm⟩
    · have hle : Γ.dist u w ≤ 2 :=
        spanSet_subset_perpSet (x := x) (y := y) (u := u)
          ⟨by rw [SimpleGraph.dist_comm]; exact hux,
            by rw [SimpleGraph.dist_comm]; exact huy⟩ hw
      have hne0 : Γ.dist u w ≠ 0 := by
        intro h0
        exact hwu ((hP.connected.dist_eq_zero_iff).mp h0).symm
      have hne1 : Γ.dist u w ≠ 1 := by
        intro h1
        have hne := c.valid (SimpleGraph.dist_eq_one_iff_adj.mp h1)
        exact hne (hcu.trans hcw.symm)
      have huw : Γ.dist u w = 2 := by omega
      obtain ⟨v, hv, -⟩ :=
        existsUnique_commonNeighbor_of_pairwise_dist_two hP huz huw h2
      have hvL : v = commonNeighbor hP huz :=
        (existsUnique_commonNeighbor hP huz).unique ⟨hv.1, hv.2.1⟩
          ⟨commonNeighbor_adj_left hP huz, commonNeighbor_adj_right hP huz⟩
      exact ⟨w, hw, by rw [← hvL]; exact hv.2.2.symm⟩
  · rintro ⟨w, hw, hLw⟩
    refine ⟨w, hw, ?_⟩
    have hzL : Γ.Adj z (commonNeighbor hP huz) := commonNeighbor_adj_right hP huz
    have htri := hP.connected.dist_triangle (u := z) (v := commonNeighbor hP huz) (w := w)
    have h1 : Γ.dist z (commonNeighbor hP huz) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hzL
    have h2 : Γ.dist (commonNeighbor hP huz) w = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hLw
    omega

end ClosureViaLines

section BlockCard

variable {Γ : SimpleGraph V}

theorem ncard_linesThrough_spanSet [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) {u a b : V}
    (hua : Γ.dist u a = 2) (hub : Γ.dist u b = 2) (hab : Γ.dist a b = 4) :
    (linesThrough Γ u (spanSet Γ a b)).ncard = (spanSet Γ a b).ncard := by
  classical
  have hu : u ∈ traceSet Γ a b :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hua,
      by rw [SimpleGraph.dist_comm]; exact hub⟩
  have hdist : ∀ w ∈ spanSet Γ a b, Γ.dist u w = 2 := fun w hw => by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT hab hw hu
  let f : ∀ w ∈ spanSet Γ a b, V := fun w hw => commonNeighbor hP (hdist w hw)
  refine (Set.ncard_congr (s := spanSet Γ a b)
    (t := linesThrough Γ u (spanSet Γ a b)) f ?_ ?_ ?_).symm
  · intro w hw
    exact ⟨commonNeighbor_adj_left hP (hdist w hw), w, hw,
      (commonNeighbor_adj_right hP (hdist w hw)).symm⟩
  · intro w w' hw hw' heq
    by_contra hne
    have h4 : Γ.dist w w' = 4 := dist_eq_four_of_mem_span hP hT hab hw hw' hne
    have hLw : Γ.Adj (f w hw) w := (commonNeighbor_adj_right hP (hdist w hw)).symm
    have hLw' : Γ.Adj (f w' hw') w' := (commonNeighbor_adj_right hP (hdist w' hw')).symm
    rw [heq] at hLw
    have hle : Γ.dist w w' ≤ 2 := by
      have htri := hP.connected.dist_triangle (u := w) (v := f w' hw') (w := w')
      have h1 : Γ.dist w (f w' hw') = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hLw.symm
      have h2 : Γ.dist (f w' hw') w' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLw'
      omega
    omega
  · intro L hL
    rw [mem_linesThrough] at hL
    obtain ⟨hLu, w, hw, hLw⟩ := hL
    exact ⟨w, hw, (eq_commonNeighbor hP (hdist w hw) hLu hLw.symm).symm⟩

theorem ncard_linesThrough_spanSet_eq [Fintype V] [DecidableRel Γ.Adj]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {u a b : V} {p : ℕ}
    (hu : c u = 0)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    (hua : Γ.dist u a = 2) (hub : Γ.dist u b = 2) (hab : Γ.dist a b = 4) :
    (linesThrough Γ u (spanSet Γ a b)).ncard = p + 1 := by
  have ha0 : c a = 0 := by
    rw [← hu]
    exact ((hP.eq_iff_even_dist c u a).2 (by rw [hua]; norm_num)).symm
  rw [ncard_linesThrough_spanSet hP hT hua hub hab, hp a b ha0 hab]

end BlockCard

section StepA

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem linesThrough_spanSet_eq_of_mem_linesThrough
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {u a b r : V} {p : ℕ}
    (hu : c u = 0) (hH : HasPropertyH Γ u)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    (hua : Γ.dist u a = 2) (hub : Γ.dist u b = 2) (hur : Γ.dist u r = 2)
    (hab : Γ.dist a b = 4)
    (hne : commonNeighbor hP hua ≠ commonNeighbor hP hur)
    (hmem : commonNeighbor hP hur ∈ linesThrough Γ u (spanSet Γ a b)) :
    linesThrough Γ u (spanSet Γ a r) = linesThrough Γ u (spanSet Γ a b) := by
  classical
  have har : Γ.dist a r = 4 :=
    dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hua hur hne
  have hu_trace : u ∈ traceSet Γ a b :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hua,
      by rw [SimpleGraph.dist_comm]; exact hub⟩
  have hsub : linesThrough Γ u (spanSet Γ a b) ⊆ linesThrough Γ u (spanSet Γ a r) := by
    intro L hL
    rw [mem_linesThrough] at hL
    obtain ⟨hLu, d, hd, hLd⟩ := hL
    by_cases hLua : L = commonNeighbor hP hua
    · rw [mem_linesThrough]
      refine ⟨hLu, a, left_mem_spanSet har, ?_⟩
      rw [hLua]
      exact (commonNeighbor_adj_right hP hua).symm
    by_cases hLur : L = commonNeighbor hP hur
    · rw [mem_linesThrough]
      refine ⟨hLu, r, right_mem_spanSet har, ?_⟩
      rw [hLur]
      exact (commonNeighbor_adj_right hP hur).symm
    · have hd_dist : Γ.dist u d = 2 := by
        rw [SimpleGraph.dist_comm]
        exact dist_eq_two_of_mem_span_of_mem_trace hP hT hab hd hu_trace
      have hL_eq : L = commonNeighbor hP hd_dist :=
        eq_commonNeighbor hP hd_dist hLu hLd.symm
      have hL_ne : commonNeighbor hP hur ≠ commonNeighbor hP hd_dist := by
        rw [← hL_eq]
        exact fun h => hLur h.symm
      have hrd : Γ.dist r d = 4 :=
        dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hur hd_dist hL_ne
      have hda : a ≠ d := by
        rintro rfl
        exact hLua (eq_commonNeighbor hP hua hLu hLd.symm)
      obtain ⟨had, hsp_eq, -⟩ :=
        span_eq_of_mem hP hT hab (left_mem_spanSet hab) hd hda
      rw [mem_linesThrough] at hmem
      obtain ⟨w, hw, hLw⟩ := hmem.2
      have hr_cl : r ∈ clSet Γ a d := by
        rw [mem_clSet]
        refine ⟨w, ?_, ?_⟩
        · rw [hsp_eq]
          exact hw
        · have hrL : Γ.Adj r (commonNeighbor hP hur) :=
            commonNeighbor_adj_right hP hur
          have htri := hP.connected.dist_triangle (u := r)
            (v := commonNeighbor hP hur) (w := w)
          have h1 : Γ.dist r (commonNeighbor hP hur) = 1 :=
            SimpleGraph.dist_eq_one_iff_adj.mpr hrL
          have h2 : Γ.dist (commonNeighbor hP hur) w = 1 :=
            SimpleGraph.dist_eq_one_iff_adj.mpr hLw
          omega
      have hr_cl' : r ∈ clSet Γ d a := by
        rw [clSet_comm]
        exact hr_cl
      have hd_cl : d ∈ clSet Γ a r := by
        have hH' := hH d a r hd_dist hua hur
          (by rw [SimpleGraph.dist_comm]; exact had) har
          (by rw [SimpleGraph.dist_comm]; exact hrd)
        exact hH'.mp hr_cl'
      have hL_ar : L ∈ linesThrough Γ u (spanSet Γ a r) := by
        have h :=
          (mem_clSet_iff_line_meets_span hP hT hua hur hd_dist har had hrd).mp hd_cl
        obtain ⟨w', hw', hLw'⟩ := h
        rw [mem_linesThrough]
        exact ⟨hLu, w', hw', by rw [hL_eq]; exact hLw'⟩
      exact hL_ar
  have hcard_ab : (linesThrough Γ u (spanSet Γ a b)).ncard = p + 1 :=
    ncard_linesThrough_spanSet_eq hP hT c hu hp hua hub hab
  have hcard_ar : (linesThrough Γ u (spanSet Γ a r)).ncard = p + 1 :=
    ncard_linesThrough_spanSet_eq hP hT c hu hp hua hur har
  have hcard : (linesThrough Γ u (spanSet Γ a r)).ncard =
      (linesThrough Γ u (spanSet Γ a b)).ncard := by
    rw [hcard_ar, hcard_ab]
  exact (Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard)).symm

end StepA

section StepB

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem linesThrough_spanSet_eq_of_two_lines
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {u a b a' b' L M : V} {p : ℕ}
    (hu : c u = 0) (hH : HasPropertyH Γ u)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    (hua : Γ.dist u a = 2) (hub : Γ.dist u b = 2)
    (hua' : Γ.dist u a' = 2) (hub' : Γ.dist u b' = 2)
    (hab : Γ.dist a b = 4) (ha'b' : Γ.dist a' b' = 4)
    (hL : L ∈ linesThrough Γ u (spanSet Γ a b) ∩
      linesThrough Γ u (spanSet Γ a' b'))
    (hM : M ∈ linesThrough Γ u (spanSet Γ a b) ∩
      linesThrough Γ u (spanSet Γ a' b'))
    (hLM : L ≠ M) :
    linesThrough Γ u (spanSet Γ a b) = linesThrough Γ u (spanSet Γ a' b') := by
  classical
  have hL_ab : L ∈ linesThrough Γ u (spanSet Γ a b) := hL.1
  have hL_ab' : L ∈ linesThrough Γ u (spanSet Γ a' b') := hL.2
  have hM_ab : M ∈ linesThrough Γ u (spanSet Γ a b) := hM.1
  have hM_ab' : M ∈ linesThrough Γ u (spanSet Γ a' b') := hM.2
  rw [mem_linesThrough] at hL_ab hL_ab' hM_ab hM_ab'
  obtain ⟨hLu, d1, hd1, hLd1⟩ := hL_ab
  obtain ⟨-, d1', hd1', hLd1'⟩ := hL_ab'
  obtain ⟨hMu, d2, hd2, hMd2⟩ := hM_ab
  obtain ⟨-, d2', hd2', hMd2'⟩ := hM_ab'
  have hu_trace : u ∈ traceSet Γ a b :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hua,
      by rw [SimpleGraph.dist_comm]; exact hub⟩
  have hu_trace' : u ∈ traceSet Γ a' b' :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hua',
      by rw [SimpleGraph.dist_comm]; exact hub'⟩
  have hd1_2 : Γ.dist u d1 = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT hab hd1 hu_trace
  have hd2_2 : Γ.dist u d2 = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT hab hd2 hu_trace
  have hd1'_2 : Γ.dist u d1' = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT ha'b' hd1' hu_trace'
  have hd2'_2 : Γ.dist u d2' = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT ha'b' hd2' hu_trace'
  have hLM2 : Γ.dist L M = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hLu.symm hMu hLM
  have hd12 : d1 ≠ d2 := by
    intro h
    have hMd1 : Γ.Adj M d1 := by rw [h]; exact hMd2
    have hd1u : d1 = u :=
      (existsUnique_commonNeighbor hP hLM2).unique ⟨hLd1, hMd1⟩
        ⟨hLu.symm, hMu.symm⟩
    exact not_mem_spanSet_of_mem_traceSet hP hT hab hu_trace (hd1u ▸ hd1)
  have hd1'2' : d1' ≠ d2' := by
    intro h
    have hMd1' : Γ.Adj M d1' := by rw [h]; exact hMd2'
    have hd1'u : d1' = u :=
      (existsUnique_commonNeighbor hP hLM2).unique ⟨hLd1', hMd1'⟩
        ⟨hLu.symm, hMu.symm⟩
    exact not_mem_spanSet_of_mem_traceSet hP hT ha'b' hu_trace' (hd1'u ▸ hd1')
  obtain ⟨hdist12, hspan, -⟩ := span_eq_of_mem hP hT hab hd1 hd2 hd12
  obtain ⟨hdist1'2', hspan', -⟩ := span_eq_of_mem hP hT ha'b' hd1' hd2' hd1'2'
  have hd1L : L = commonNeighbor hP hd1_2 :=
    eq_commonNeighbor hP hd1_2 hLu hLd1.symm
  have hd2M : M = commonNeighbor hP hd2_2 :=
    eq_commonNeighbor hP hd2_2 hMu hMd2.symm
  have hd1'L : L = commonNeighbor hP hd1'_2 :=
    eq_commonNeighbor hP hd1'_2 hLu hLd1'.symm
  have hd2'M : M = commonNeighbor hP hd2'_2 :=
    eq_commonNeighbor hP hd2'_2 hMu hMd2'.symm
  have hdist_d1'_d2 : Γ.dist d1' d2 = 4 :=
    dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hd1'_2 hd2_2 (by
      rw [← hd1'L, ← hd2M]
      exact hLM)
  have hmemA1 : commonNeighbor hP hd1'_2 ∈
      linesThrough Γ u (spanSet Γ d2 d1) := by
    rw [← hd1'L, spanSet_comm d2 d1, hspan]
    exact ⟨hLu, d1, hd1, hLd1⟩
  have hA1 : linesThrough Γ u (spanSet Γ d2 d1') =
      linesThrough Γ u (spanSet Γ d2 d1) :=
    linesThrough_spanSet_eq_of_mem_linesThrough hP hT c hu hH hp
      (hua := hd2_2) (hub := hd1_2) (hur := hd1'_2)
      (hab := by rw [SimpleGraph.dist_comm]; exact hdist12)
      (by rw [← hd2M, ← hd1'L]; exact hLM.symm) hmemA1
  have hmemA2 : commonNeighbor hP hd2'_2 ∈
      linesThrough Γ u (spanSet Γ d1' d2) := by
    rw [← hd2'M, spanSet_comm d1' d2, hA1, spanSet_comm d2 d1, hspan]
    exact ⟨hMu, d2, hd2, hMd2⟩
  have hA2 : linesThrough Γ u (spanSet Γ d1' d2') =
      linesThrough Γ u (spanSet Γ d1' d2) :=
    linesThrough_spanSet_eq_of_mem_linesThrough hP hT c hu hH hp
      (hua := hd1'_2) (hub := hd2_2) (hur := hd2'_2)
      (hab := hdist_d1'_d2)
      (by rw [← hd1'L, ← hd2'M]; exact hLM) hmemA2
  calc
    linesThrough Γ u (spanSet Γ a b)
        = linesThrough Γ u (spanSet Γ d1 d2) := by rw [hspan]
    _ = linesThrough Γ u (spanSet Γ d2 d1) := by rw [spanSet_comm d1 d2]
    _ = linesThrough Γ u (spanSet Γ d2 d1') := hA1.symm
    _ = linesThrough Γ u (spanSet Γ d1' d2) := by rw [spanSet_comm d2 d1']
    _ = linesThrough Γ u (spanSet Γ d1' d2') := hA2.symm
    _ = linesThrough Γ u (spanSet Γ a' b') := by rw [hspan']

end StepB

end CFSG.Geometry.GeneralizedQuadrangles
