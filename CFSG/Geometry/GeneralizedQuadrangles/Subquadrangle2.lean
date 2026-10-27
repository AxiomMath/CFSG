module

public import CFSG.Geometry.GeneralizedQuadrangles.Subquadrangle

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Recognition

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
variable {c : Γ.Coloring (Fin 2)} {P' : Set V}

theorem ncard_fullLinesThrough_eq_trace (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {P' : Set V}
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    {a b : V} (ha : a ∈ P') (hb : b ∈ P') (hab : Γ.dist a b = 4) :
    (fullLinesThrough Γ P' a).ncard = (traceSet Γ a b ∩ P').ncard := by
  classical
  have hdist : ∀ L ∈ fullLinesThrough Γ P' a, Γ.dist b L = 3 := by
    intro L hL
    have hLa : Γ.Adj a L := hL.1
    have hbL : ¬ Γ.Adj b L := by
      intro hbL
      have h1 : Γ.dist a L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hLa
      have h2 : Γ.dist L b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbL.symm
      have htri := hP.connected.dist_triangle (u := a) (v := L) (w := b)
      omega
    have hcb : c b = 0 := h0 b hb
    have hcL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero (h0 a ha) hLa
    exact dist_eq_three_of_not_adj_of_color_ne hP c hbL (by rw [hcb, hcL]; decide)
  refine Set.ncard_congr (fun L hL => proj hP (hdist L hL)) ?_ ?_ ?_
  · intro L hL
    have hLa : Γ.Adj a L := hL.1
    have hLfull : Γ.neighborSet L ⊆ P' := hL.2
    have h3 : Γ.dist b L = 3 := hdist L hL
    have hLp : Γ.Adj L (proj hP h3) := proj_adj hP h3
    have hbp : Γ.dist b (proj hP h3) = 2 := proj_dist hP h3
    have hpP : proj hP h3 ∈ P' := hLfull hLp
    have hap : Γ.dist a (proj hP h3) = 2 := by
      have hne : a ≠ proj hP h3 := by
        intro h
        rw [← h] at hbp
        rw [SimpleGraph.dist_comm] at hbp
        omega
      exact dist_eq_two_of_adj_of_adj_of_ne hP hLa hLp hne
    exact ⟨⟨hap, hbp⟩, hpP⟩
  · intro L L' hL hL' heq
    have h3 : Γ.dist b L = 3 := hdist L hL
    have h3' : Γ.dist b L' = 3 := hdist L' hL'
    have hLa : Γ.Adj a L := hL.1
    have hLa' : Γ.Adj a L' := hL'.1
    have hLw : Γ.Adj L (proj hP h3) := proj_adj hP h3
    have hL'w : Γ.Adj L' (proj hP h3') := proj_adj hP h3'
    have hwa : proj hP h3 ≠ a := by
      intro h
      have hbp : Γ.dist b (proj hP h3) = 2 := proj_dist hP h3
      rw [h] at hbp
      rw [SimpleGraph.dist_comm] at hbp
      omega
    have hL'w' : Γ.Adj L' (proj hP h3) := heq.symm ▸ hL'w
    exact eq_of_two_common_points hP (Ne.symm hwa) hLa.symm hLw hLa'.symm hL'w'
  · intro w hw
    obtain ⟨hwmem, hwP⟩ := hw
    have haw : Γ.dist a w = 2 := hwmem.1
    have hbw : Γ.dist b w = 2 := hwmem.2
    let L := commonNeighbor hP haw
    have haL : Γ.Adj a L := commonNeighbor_adj_left hP haw
    have hwL : Γ.Adj L w := (commonNeighbor_adj_right hP haw).symm
    have hLfull : Γ.neighborSet L ⊆ P' := by
      have hne : a ≠ w := by
        intro h
        rw [h] at haw
        simp at haw
      have h2' : 1 < (Γ.neighborSet L ∩ P').ncard :=
        (Set.one_lt_ncard (s := Γ.neighborSet L ∩ P')).mpr
          ⟨a, ⟨haL.symm, ha⟩, w, ⟨hwL, hwP⟩, hne⟩
      exact hfull L (color_eq_one_of_adj_of_color_eq_zero (h0 a ha) haL) (by omega)
    have hLmem : L ∈ fullLinesThrough Γ P' a := ⟨haL, hLfull⟩
    refine ⟨L, hLmem, ?_⟩
    have h3 : Γ.dist b L = 3 := hdist L hLmem
    exact (eq_proj hP h3 hwL hbw).symm

theorem ncard_fullLinesThrough_eq_trace_swap (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {P' : Set V}
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    {a b : V} (ha : a ∈ P') (hb : b ∈ P') (hab : Γ.dist a b = 4) :
    (fullLinesThrough Γ P' b).ncard = (traceSet Γ a b ∩ P').ncard := by
  have h4 : Γ.dist b a = 4 := by rw [SimpleGraph.dist_comm]; exact hab
  have hsym : traceSet Γ b a = traceSet Γ a b := by
    ext w
    simp only [mem_traceSet]
    exact and_comm
  rw [← hsym]
  exact ncard_fullLinesThrough_eq_trace hP c h0 hfull hb ha h4

theorem ncard_fullLinesThrough_eq_of_dist_four (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {P' : Set V}
    (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    {a b : V} (ha : a ∈ P') (hb : b ∈ P') (hab : Γ.dist a b = 4) :
    (fullLinesThrough Γ P' a).ncard = (fullLinesThrough Γ P' b).ncard := by
  rw [ncard_fullLinesThrough_eq_trace hP c h0 hfull ha hb hab,
    ncard_fullLinesThrough_eq_trace_swap hP c h0 hfull ha hb hab]

theorem ncard_fullLinesThrough_eq_of_dist_two (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (F : QuadrangleFrame Γ P') (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    {a b : V} (ha : a ∈ P') (hb : b ∈ P') (hab : Γ.dist a b = 2) :
    (fullLinesThrough Γ P' a).ncard = (fullLinesThrough Γ P' b).ncard := by
  classical
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have hab_ne : a ≠ b := by
    intro h
    rw [h] at hab
    simp at hab
  let E := commonNeighbor hP hab
  have haE : Γ.Adj a E := commonNeighbor_adj_left hP hab
  have hbE : Γ.Adj b E := commonNeighbor_adj_right hP hab
  have hEfull : Γ.neighborSet E ⊆ P' := by
    have h2' : 1 < (Γ.neighborSet E ∩ P').ncard :=
      (Set.one_lt_ncard (s := Γ.neighborSet E ∩ P')).mpr
        ⟨a, ⟨haE.symm, ha⟩, b, ⟨hbE.symm, hb⟩, hab_ne⟩
    exact hfull E (color_eq_one_of_adj_of_color_eq_zero (h0 a ha) haE) (by omega)
  have hn2 : 1 < (fullLinesThrough Γ P' a).ncard := by
    have := two_le_ncard_fullLinesThrough hP F h0 hfull ha
    omega
  obtain ⟨L1, hL1, L2, hL2, hL12⟩ :=
    (Set.one_lt_ncard (s := fullLinesThrough Γ P' a)).mp hn2
  have hEmem : E ∈ fullLinesThrough Γ P' a := ⟨haE, hEfull⟩
  obtain ⟨L, hLmem, hLne⟩ : ∃ L, L ∈ fullLinesThrough Γ P' a ∧ L ≠ E := by
    by_cases h1 : L1 = E
    · exact ⟨L2, hL2, fun h => hL12 (h1.trans h.symm)⟩
    · exact ⟨L1, hL1, h1⟩
  have hLa : Γ.Adj a L := hLmem.1
  have hLfull : Γ.neighborSet L ⊆ P' := hLmem.2
  have hcL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero (h0 a ha) hLa
  have hLdeg : Γ.degree L = s + 1 := by
    rw [hdeg L, if_neg (by rw [hcL]; decide)]
  have hNpos : 1 < (Γ.neighborSet L).ncard := by
    rw [ncard_neighborSet, hLdeg]
    omega
  obtain ⟨e, heN, hea⟩ := Set.exists_ne_of_one_lt_ncard hNpos a
  have heP : e ∈ P' := hLfull heN
  have hbe4 : Γ.dist b e = 4 := by
    have hle : Γ.dist b e ≤ 4 := hP.dist_le (by norm_num) b e
    have hcb : c b = 0 := h0 b hb
    have hce : c e = 0 := h0 e heP
    have heven : Even (Γ.dist b e) :=
      (hP.eq_iff_even_dist c b e).1 (by rw [hcb, hce])
    have hbLnot : ¬ Γ.Adj b L := by
      intro hbL
      have hLE : L = E :=
        eq_of_two_common_points hP hab_ne hLa.symm hbL.symm haE.symm hbE.symm
      exact hLne hLE
    have hbL3 : Γ.dist b L = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hbLnot
        (by rw [hcb, hcL]; decide)
    have hne0 : Γ.dist b e ≠ 0 := by
      intro h0d
      have hbe : b = e := (hP.connected.dist_eq_zero_iff).mp h0d
      exact hbLnot (by rw [hbe]; exact heN.symm)
    have hne2 : Γ.dist b e ≠ 2 := by
      intro h2
      have hproj_e : e = proj hP hbL3 := eq_proj hP hbL3 heN h2
      have hproj_a : a = proj hP hbL3 :=
        eq_proj hP hbL3 hLa.symm (by rw [SimpleGraph.dist_comm]; exact hab)
      exact hea (hproj_e.trans hproj_a.symm)
    obtain ⟨k, hk⟩ := heven
    omega
  have hn2e : 1 < (fullLinesThrough Γ P' e).ncard := by
    have := two_le_ncard_fullLinesThrough hP F h0 hfull heP
    omega
  obtain ⟨M1, hM1, M2, hM2, hM12⟩ :=
    (Set.one_lt_ncard (s := fullLinesThrough Γ P' e)).mp hn2e
  have hLmemE : L ∈ fullLinesThrough Γ P' e := ⟨heN.symm, hLfull⟩
  obtain ⟨M, hMmem, hMne⟩ : ∃ M, M ∈ fullLinesThrough Γ P' e ∧ M ≠ L := by
    by_cases h1 : M1 = L
    · exact ⟨M2, hM2, fun h => hM12 (h1.trans h.symm)⟩
    · exact ⟨M1, hM1, h1⟩
  have hMe : Γ.Adj e M := hMmem.1
  have hMfull : Γ.neighborSet M ⊆ P' := hMmem.2
  have hcM : c M = 1 := color_eq_one_of_adj_of_color_eq_zero (h0 e heP) hMe
  have hMdeg : Γ.degree M = s + 1 := by
    rw [hdeg M, if_neg (by rw [hcM]; decide)]
  have hbMnot : ¬ Γ.Adj b M := by
    intro hbM
    have hbe_ne : b ≠ e := by
      intro h
      rw [h] at hbe4
      simp at hbe4
    have h2 : Γ.dist b e = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hbM hMe.symm hbe_ne
    omega
  have hbM3 : Γ.dist b M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hbMnot
      (by rw [h0 b hb, hcM]; decide)
  let w := proj hP hbM3
  have hMw : Γ.Adj M w := proj_adj hP hbM3
  have hbw : Γ.dist b w = 2 := proj_dist hP hbM3
  have hwP : w ∈ P' := hMfull hMw
  have hew : e ≠ w := by
    intro h
    rw [← h] at hbw
    omega
  have hNMc : ({e, w} : Set V).ncard < (Γ.neighborSet M).ncard := by
    rw [Set.ncard_pair hew, ncard_neighborSet, hMdeg]
    omega
  obtain ⟨d, hdN, hdnot⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hNMc (Set.toFinite ({e, w} : Set V))
  have hde : d ≠ e := by
    intro h
    exact hdnot (by rw [h]; simp)
  have hdw : d ≠ w := by
    intro h
    exact hdnot (by rw [h]; simp)
  have hdP : d ∈ P' := hMfull hdN
  have haMnot : ¬ Γ.Adj a M := by
    intro haM
    have hML : M = L :=
      eq_of_two_common_points hP (Ne.symm hea) haM.symm hMe.symm hLa.symm heN
    exact hMne hML
  have haM3 : Γ.dist a M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c haMnot
      (by rw [h0 a ha, hcM]; decide)
  have hae2 : Γ.dist a e = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hLa heN (Ne.symm hea)
  have hproj_e : e = proj hP haM3 := eq_proj hP haM3 hMe.symm hae2
  have had4 : Γ.dist a d = 4 := by
    have hle : Γ.dist a d ≤ 4 := hP.dist_le (by norm_num) a d
    have hca : c a = 0 := h0 a ha
    have hcd : c d = 0 := h0 d hdP
    have heven : Even (Γ.dist a d) :=
      (hP.eq_iff_even_dist c a d).1 (by rw [hca, hcd])
    have hne0 : Γ.dist a d ≠ 0 := by
      intro h0d
      have had : a = d := (hP.connected.dist_eq_zero_iff).mp h0d
      exact haMnot (by rw [had]; exact (show Γ.Adj M d from hdN).symm)
    have hne2 : Γ.dist a d ≠ 2 := by
      intro h2
      have hproj_d : d = proj hP haM3 := eq_proj hP haM3 hdN h2
      exact hde (hproj_d.trans hproj_e.symm)
    obtain ⟨k, hk⟩ := heven
    omega
  have hbd4 : Γ.dist b d = 4 := by
    have hle : Γ.dist b d ≤ 4 := hP.dist_le (by norm_num) b d
    have hcb : c b = 0 := h0 b hb
    have hcd : c d = 0 := h0 d hdP
    have heven : Even (Γ.dist b d) :=
      (hP.eq_iff_even_dist c b d).1 (by rw [hcb, hcd])
    have hne0 : Γ.dist b d ≠ 0 := by
      intro h0d
      have hbd : b = d := (hP.connected.dist_eq_zero_iff).mp h0d
      exact hbMnot (by rw [hbd]; exact (show Γ.Adj M d from hdN).symm)
    have hne2 : Γ.dist b d ≠ 2 := by
      intro h2
      have hproj_d : d = proj hP hbM3 := eq_proj hP hbM3 hdN h2
      exact hdw (by simpa [w] using hproj_d)
    obtain ⟨k, hk⟩ := heven
    omega
  calc
    (fullLinesThrough Γ P' a).ncard = (fullLinesThrough Γ P' d).ncard :=
      ncard_fullLinesThrough_eq_of_dist_four hP c h0 hfull ha hdP had4
    _ = (fullLinesThrough Γ P' b).ncard :=
      ncard_fullLinesThrough_eq_of_dist_four hP c h0 hfull hdP hb
        (by rw [SimpleGraph.dist_comm]; exact hbd4)

theorem ncard_fullLinesThrough_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (F : QuadrangleFrame Γ P') (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    {a b : V} (ha : a ∈ P') (hb : b ∈ P') :
    (fullLinesThrough Γ P' a).ncard = (fullLinesThrough Γ P' b).ncard := by
  have hle : Γ.dist a b ≤ 4 := hP.dist_le (by norm_num) a b
  have heven : Even (Γ.dist a b) := by
    have hca : c a = 0 := h0 a ha
    have hcb : c b = 0 := h0 b hb
    exact (hP.eq_iff_even_dist c a b).1 (by rw [hca, hcb])
  obtain ⟨k, hk⟩ := heven
  have hk_le : k ≤ 2 := by omega
  interval_cases k
  · have hk0 : Γ.dist a b = 0 := by omega
    have hab : a = b := (hP.connected.dist_eq_zero_iff).mp hk0
    subst hab
    rfl
  · have hk2 : Γ.dist a b = 2 := by omega
    exact ncard_fullLinesThrough_eq_of_dist_two hP hT c hdeg F h0 hfull ha hb hk2
  · have hk4 : Γ.dist a b = 4 := by omega
    exact ncard_fullLinesThrough_eq_of_dist_four hP c h0 hfull ha hb hk4

theorem exists_isFullSubquadrangle (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {P' : Set V} (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    (hquad : ∃ x ∈ P', ∃ y ∈ P', Γ.dist x y = 4 ∧
      2 ≤ (traceSet Γ x y ∩ P').ncard) :
    ∃ t' : ℕ, 1 ≤ t' ∧ IsFullSubquadrangle c P' t' := by
  classical
  have hquad' := hquad
  obtain ⟨x, hx, y, hy, hxy, htr⟩ := hquad'
  obtain ⟨F⟩ := exists_quadrangleFrame hP hquad
  have hconst : ∀ {a b : V}, a ∈ P' → b ∈ P' →
      (fullLinesThrough Γ P' a).ncard = (fullLinesThrough Γ P' b).ncard :=
    fun ha hb => ncard_fullLinesThrough_eq hP hT c hdeg F h0 hfull ha hb
  have hx2 : 2 ≤ (fullLinesThrough Γ P' x).ncard :=
    two_le_ncard_fullLinesThrough hP F h0 hfull hx
  refine ⟨(fullLinesThrough Γ P' x).ncard - 1, by omega, h0, hfull, ?_, hquad⟩
  intro a ha
  change (fullLinesThrough Γ P' a).ncard =
    (fullLinesThrough Γ P' x).ncard - 1 + 1
  rw [hconst ha hx]
  omega


theorem exists_walk_subquadrangleGraph (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (F : QuadrangleFrame Γ P') (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    {a b : V} (ha : a ∈ subquadrangleSet Γ c P')
    (hb : b ∈ subquadrangleSet Γ c P') :
    ∃ p : (Γ.induce (subquadrangleSet Γ c P')).Walk ⟨a, ha⟩ ⟨b, hb⟩,
      p.length = Γ.dist a b := by
  classical
  have build : ∀ {u v : V} (hu : u ∈ subquadrangleSet Γ c P')
      (hv : v ∈ subquadrangleSet Γ c P') (w : Γ.Walk u v)
      (hw : ∀ x ∈ w.support, x ∈ subquadrangleSet Γ c P')
      (hlen : w.length = Γ.dist u v),
      ∃ p : (Γ.induce (subquadrangleSet Γ c P')).Walk ⟨u, hu⟩ ⟨v, hv⟩,
        p.length = Γ.dist u v := by
    intro u v hu hv w hw hlen
    have hind : (w.induce (subquadrangleSet Γ c P') hw).length = w.length := by
      have hmap : ((w.induce (subquadrangleSet Γ c P') hw).map
          (Embedding.induce (subquadrangleSet Γ c P')).toHom).length =
          (w.induce (subquadrangleSet Γ c P') hw).length :=
        SimpleGraph.Walk.length_map _ _
      rw [SimpleGraph.Walk.map_induce] at hmap
      exact hmap.symm
    refine ⟨(w.induce (subquadrangleSet Γ c P') hw).copy
      (Subtype.ext rfl) (Subtype.ext rfl), ?_⟩
    rw [SimpleGraph.Walk.length_copy, hind]
    exact hlen
  have hdle : Γ.dist a b ≤ 4 := hP.dist_le (by norm_num) a b
  have hcase := hdle
  interval_cases hd : Γ.dist a b
  · have hab : a = b := (hP.connected.dist_eq_zero_iff).mp hd
    subst hab
    rw [← hd]
    refine build ha hb SimpleGraph.Walk.nil ?_ ?_
    · intro x hx
      rw [SimpleGraph.Walk.mem_support_nil_iff] at hx
      subst hx
      exact ha
    · simp [hd]
  · have hadj : Γ.Adj a b := SimpleGraph.dist_eq_one_iff_adj.mp hd
    rw [← hd]
    refine build ha hb (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil) ?_ ?_
    · intro x hx
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · simp [hd]
  · rcases (mem_subquadrangleSet.mp ha) with haP | haL <;>
      rcases (mem_subquadrangleSet.mp hb) with hbP | hbL
    ·
      have hca : c a = 0 := h0 a haP
      have hcb : c b = 0 := h0 b hbP
      let m := commonNeighbor hP hd
      have ham : Γ.Adj a m := commonNeighbor_adj_left hP hd
      have hbm : Γ.Adj b m := commonNeighbor_adj_right hP hd
      have hcm : c m = 1 := color_eq_one_of_adj_of_color_eq_zero hca ham
      have hmfull : Γ.neighborSet m ⊆ P' := by
        have hne : a ≠ b := by
          intro h
          rw [h] at hd
          simp at hd
        have h2' : 1 < (Γ.neighborSet m ∩ P').ncard :=
          (Set.one_lt_ncard (s := Γ.neighborSet m ∩ P')).mpr
            ⟨a, ⟨ham.symm, haP⟩, b, ⟨hbm.symm, hbP⟩, hne⟩
        exact hfull m hcm (by omega)
      have hmS : m ∈ subquadrangleSet Γ c P' := by
        rw [mem_subquadrangleSet]
        exact Or.inr ⟨hcm, hmfull⟩
      rw [← hd]
      refine build ha hb (SimpleGraph.Walk.cons ham
        (SimpleGraph.Walk.cons hbm.symm SimpleGraph.Walk.nil)) ?_ ?_
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ha
        · exact hmS
        · exact hb
      · simp [hd]
    ·
      have hca : c a = 0 := h0 a haP
      have hcb : c b = 1 := hbL.1
      have heven : Even (Γ.dist a b) := by rw [hd]; exact ⟨1, by norm_num⟩
      have hcab : c a = c b := (hP.eq_iff_even_dist c a b).2 heven
      exact absurd (hca.symm.trans (hcab.trans hcb)) (by decide)
    ·
      have hca : c a = 1 := haL.1
      have hcb : c b = 0 := h0 b hbP
      have heven : Even (Γ.dist a b) := by rw [hd]; exact ⟨1, by norm_num⟩
      have hcab : c a = c b := (hP.eq_iff_even_dist c a b).2 heven
      exact absurd (hca.symm.trans (hcab.trans hcb)) (by decide)
    ·
      let m := commonNeighbor hP hd
      have ham : Γ.Adj a m := commonNeighbor_adj_left hP hd
      have hbm : Γ.Adj b m := commonNeighbor_adj_right hP hd
      have hmP : m ∈ P' := haL.2 ham
      have hmS : m ∈ subquadrangleSet Γ c P' := Or.inl hmP
      rw [← hd]
      refine build ha hb (SimpleGraph.Walk.cons ham
        (SimpleGraph.Walk.cons hbm.symm SimpleGraph.Walk.nil)) ?_ ?_
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ha
        · exact hmS
        · exact hb
      · simp [hd]
  · rcases (mem_subquadrangleSet.mp ha) with haP | haL <;>
      rcases (mem_subquadrangleSet.mp hb) with hbP | hbL
    ·
      have hca : c a = 0 := h0 a haP
      have hcb : c b = 0 := h0 b hbP
      have hodd : Odd (Γ.dist a b) := by rw [hd]; exact ⟨1, by norm_num⟩
      have hcab : c a ≠ c b := by
        intro h
        exact (Nat.not_even_iff_odd.mpr hodd) ((hP.eq_iff_even_dist c a b).1 h)
      exact absurd (hca.trans hcb.symm) hcab
    ·
      have hca : c a = 0 := h0 a haP
      let w := proj hP hd
      have hbw : Γ.Adj b w := proj_adj hP hd
      have haw : Γ.dist a w = 2 := proj_dist hP hd
      have hwP : w ∈ P' := hbL.2 hbw
      let m := commonNeighbor hP haw
      have ham : Γ.Adj a m := commonNeighbor_adj_left hP haw
      have hwm : Γ.Adj w m := commonNeighbor_adj_right hP haw
      have hcm : c m = 1 := color_eq_one_of_adj_of_color_eq_zero hca ham
      have hmfull : Γ.neighborSet m ⊆ P' := by
        have hne : a ≠ w := by
          intro h
          rw [h] at haw
          simp at haw
        have h2' : 1 < (Γ.neighborSet m ∩ P').ncard :=
          (Set.one_lt_ncard (s := Γ.neighborSet m ∩ P')).mpr
            ⟨a, ⟨ham.symm, haP⟩, w, ⟨hwm.symm, hwP⟩, hne⟩
        exact hfull m hcm (by omega)
      have hmS : m ∈ subquadrangleSet Γ c P' := by
        rw [mem_subquadrangleSet]
        exact Or.inr ⟨hcm, hmfull⟩
      rw [← hd]
      refine build ha hb (SimpleGraph.Walk.cons ham
        (SimpleGraph.Walk.cons hwm.symm
          (SimpleGraph.Walk.cons hbw.symm SimpleGraph.Walk.nil))) ?_ ?_
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ha
        · exact hmS
        · exact Or.inl hwP
        · exact hb
      · simp [hd]
    ·
      have hca : c a = 1 := haL.1
      have hba3 : Γ.dist b a = 3 := by rw [SimpleGraph.dist_comm]; exact hd
      let w := proj hP hba3
      have haw : Γ.Adj a w := proj_adj hP hba3
      have hbw : Γ.dist b w = 2 := proj_dist hP hba3
      have hwP : w ∈ P' := haL.2 haw
      let m := commonNeighbor hP hbw
      have hbm : Γ.Adj b m := commonNeighbor_adj_left hP hbw
      have hwm : Γ.Adj w m := commonNeighbor_adj_right hP hbw
      have hcm : c m = 1 := color_eq_one_of_adj_of_color_eq_zero (h0 b hbP) hbm
      have hmfull : Γ.neighborSet m ⊆ P' := by
        have hne : b ≠ w := by
          intro h
          rw [h] at hbw
          simp at hbw
        have h2' : 1 < (Γ.neighborSet m ∩ P').ncard :=
          (Set.one_lt_ncard (s := Γ.neighborSet m ∩ P')).mpr
            ⟨b, ⟨hbm.symm, hbP⟩, w, ⟨hwm.symm, hwP⟩, hne⟩
        exact hfull m hcm (by omega)
      have hmS : m ∈ subquadrangleSet Γ c P' := by
        rw [mem_subquadrangleSet]
        exact Or.inr ⟨hcm, hmfull⟩
      rw [← hd]
      refine build ha hb (SimpleGraph.Walk.cons haw
        (SimpleGraph.Walk.cons hwm
          (SimpleGraph.Walk.cons hbm.symm SimpleGraph.Walk.nil))) ?_ ?_
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ha
        · exact Or.inl hwP
        · exact hmS
        · exact hb
      · simp [hd]
    ·
      have hca : c a = 1 := haL.1
      have hcb : c b = 1 := hbL.1
      have hodd : Odd (Γ.dist a b) := by rw [hd]; exact ⟨1, by norm_num⟩
      have hcab : c a ≠ c b := by
        intro h
        exact (Nat.not_even_iff_odd.mpr hodd) ((hP.eq_iff_even_dist c a b).1 h)
      exact absurd (hca.trans hcb.symm) hcab
  · rcases (mem_subquadrangleSet.mp ha) with haP | haL <;>
      rcases (mem_subquadrangleSet.mp hb) with hbP | hbL
    ·
      obtain ⟨L, haL, hLfull⟩ := exists_fullLineThrough hP F h0 hfull haP
      have hLmem : L ∈ fullLinesThrough Γ P' a := ⟨haL, hLfull⟩
      have hbLnot : ¬ Γ.Adj b L := by
        intro hbL
        have h1 : Γ.dist a L = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr haL
        have h2 : Γ.dist L b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbL.symm
        have htri := hP.connected.dist_triangle (u := a) (v := L) (w := b)
        omega
      have hcb : c b = 0 := h0 b hbP
      have hcL : c L = 1 := color_eq_one_of_adj_of_color_eq_zero (h0 a haP) haL
      have hbL3 : Γ.dist b L = 3 :=
        dist_eq_three_of_not_adj_of_color_ne hP c hbLnot (by rw [hcb, hcL]; decide)
      let w := proj hP hbL3
      have hLw : Γ.Adj L w := proj_adj hP hbL3
      have hbw : Γ.dist b w = 2 := proj_dist hP hbL3
      have hwP : w ∈ P' := hLfull hLw
      let m := commonNeighbor hP hbw
      have hbm : Γ.Adj b m := commonNeighbor_adj_left hP hbw
      have hwm : Γ.Adj w m := commonNeighbor_adj_right hP hbw
      have hcm : c m = 1 := color_eq_one_of_adj_of_color_eq_zero hcb hbm
      have hmfull : Γ.neighborSet m ⊆ P' := by
        have hne : b ≠ w := by
          intro h
          rw [h] at hbw
          simp at hbw
        have h2' : 1 < (Γ.neighborSet m ∩ P').ncard :=
          (Set.one_lt_ncard (s := Γ.neighborSet m ∩ P')).mpr
            ⟨b, ⟨hbm.symm, hbP⟩, w, ⟨hwm.symm, hwP⟩, hne⟩
        exact hfull m hcm (by omega)
      have hmS : m ∈ subquadrangleSet Γ c P' := by
        rw [mem_subquadrangleSet]
        exact Or.inr ⟨hcm, hmfull⟩
      rw [← hd]
      refine build ha hb (SimpleGraph.Walk.cons haL
        (SimpleGraph.Walk.cons hLw
          (SimpleGraph.Walk.cons hwm
            (SimpleGraph.Walk.cons hbm.symm SimpleGraph.Walk.nil)))) ?_ ?_
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact ha
        · exact Or.inr ⟨hcL, hLfull⟩
        · exact Or.inl hwP
        · exact hmS
        · exact hb
      · simp [hd]
    ·
      have hca : c a = 0 := h0 a haP
      have hcb : c b = 1 := hbL.1
      have heven : Even (Γ.dist a b) := by rw [hd]; exact ⟨2, by norm_num⟩
      have hcab : c a = c b := (hP.eq_iff_even_dist c a b).2 heven
      exact absurd (hca.symm.trans (hcab.trans hcb)) (by decide)
    ·
      have hca : c a = 1 := haL.1
      have hcb : c b = 0 := h0 b hbP
      have heven : Even (Γ.dist a b) := by rw [hd]; exact ⟨2, by norm_num⟩
      have hcab : c a = c b := (hP.eq_iff_even_dist c a b).2 heven
      exact absurd (hca.symm.trans (hcab.trans hcb)) (by decide)
    ·
      have hspos : 0 < (Γ.neighborSet a).ncard := by
        have hs : 2 ≤ s := two_le_s hP hT c hdeg
        rw [ncard_neighborSet, hdeg a, if_neg (by rw [haL.1]; decide)]
        omega
      obtain ⟨x, hxN⟩ := (Set.ncard_pos (Set.toFinite _)).mp hspos
      have hax : Γ.Adj a x := hxN
      have hxP : x ∈ P' := haL.2 hax
      have hbXnot : ¬ Γ.Adj b x := by
        intro hbx
        have h1 : Γ.dist a x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hax
        have h2 : Γ.dist x b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbx.symm
        have htri := hP.connected.dist_triangle (u := a) (v := x) (w := b)
        omega
      have hca : c a = 1 := haL.1
      have hcx : c x = 0 := h0 x hxP
      have hxb3 : Γ.dist x b = 3 :=
        dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hbXnot h.symm)
        (by rw [hcx, hbL.1]; decide)
      let w := proj hP hxb3
      have hbw : Γ.Adj b w := proj_adj hP hxb3
      have hxw : Γ.dist x w = 2 := proj_dist hP hxb3
      have hwP : w ∈ P' := hbL.2 hbw
      let m := commonNeighbor hP hxw
      have hxm : Γ.Adj x m := commonNeighbor_adj_left hP hxw
      have hwm : Γ.Adj w m := commonNeighbor_adj_right hP hxw
      have hcm : c m = 1 := color_eq_one_of_adj_of_color_eq_zero hcx hxm
      have hmfull : Γ.neighborSet m ⊆ P' := by
        have hne : x ≠ w := by
          intro h
          rw [h] at hxw
          simp at hxw
        have h2' : 1 < (Γ.neighborSet m ∩ P').ncard :=
          (Set.one_lt_ncard (s := Γ.neighborSet m ∩ P')).mpr
            ⟨x, ⟨hxm.symm, hxP⟩, w, ⟨hwm.symm, hwP⟩, hne⟩
        exact hfull m hcm (by omega)
      have hmS : m ∈ subquadrangleSet Γ c P' := by
        rw [mem_subquadrangleSet]
        exact Or.inr ⟨hcm, hmfull⟩
      rw [← hd]
      refine build ha hb (SimpleGraph.Walk.cons hax
        (SimpleGraph.Walk.cons hxm
          (SimpleGraph.Walk.cons hwm.symm
            (SimpleGraph.Walk.cons hbw.symm SimpleGraph.Walk.nil)))) ?_ ?_
      · intro x' hx'
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx'
        rcases hx' with rfl | rfl | rfl | rfl | rfl
        · exact ha
        · exact Or.inl hxP
        · exact hmS
        · exact Or.inl hwP
        · exact hb
      · simp [hd]

theorem dist_subquadrangleGraph (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (F : QuadrangleFrame Γ P') (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    {a b : V} (ha : a ∈ subquadrangleSet Γ c P')
    (hb : b ∈ subquadrangleSet Γ c P') :
    (Γ.induce (subquadrangleSet Γ c P')).dist ⟨a, ha⟩ ⟨b, hb⟩ = Γ.dist a b := by
  classical
  obtain ⟨p, hp⟩ := exists_walk_subquadrangleGraph hP hT c hdeg F h0 hfull ha hb
  have hupper : (Γ.induce (subquadrangleSet Γ c P')).dist ⟨a, ha⟩ ⟨b, hb⟩ ≤
      Γ.dist a b := by
    rw [← hp]
    exact SimpleGraph.dist_le p
  have hlower : Γ.dist a b ≤
      (Γ.induce (subquadrangleSet Γ c P')).dist ⟨a, ha⟩ ⟨b, hb⟩ := by
    have hreach : (Γ.induce (subquadrangleSet Γ c P')).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := ⟨p⟩
    obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    have hmap := Γ.dist_le (q.map (Embedding.induce (subquadrangleSet Γ c P')).toHom)
    rw [SimpleGraph.Walk.length_map, hq] at hmap
    exact hmap
  exact le_antisymm hupper hlower


theorem dist_subquadrangleGraph_of_isFullSubquadrangle (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {t' : ℕ} {P' : Set V} (hF : IsFullSubquadrangle c P' t')
    {a b : V} (ha : a ∈ subquadrangleSet Γ c P')
    (hb : b ∈ subquadrangleSet Γ c P') :
    (Γ.induce (subquadrangleSet Γ c P')).dist ⟨a, ha⟩ ⟨b, hb⟩ = Γ.dist a b := by
  obtain ⟨F⟩ := exists_quadrangleFrame hP hF.2.2.2
  exact dist_subquadrangleGraph hP hT c hdeg F hF.1 hF.2.1 ha hb

theorem isGeneralizedPolygon_subquadrangleGraph (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {t' : ℕ} {P' : Set V} (hF : IsFullSubquadrangle c P' t') :
    IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 := by
  classical
  have h0 : ∀ x ∈ P', c x = 0 := hF.1
  have hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P' := hF.2.1
  obtain ⟨F⟩ := exists_quadrangleFrame hP hF.2.2.2
  let S : Set V := subquadrangleSet Γ c P'
  have hxS : F.x ∈ S := Or.inl F.hx
  have hyS : F.y ∈ S := Or.inl F.hy
  haveI hSne : Nonempty S := ⟨⟨F.x, hxS⟩⟩
  have hconn : (Γ.induce S).Connected :=
    ⟨fun u v => by
      obtain ⟨p, -⟩ := exists_walk_subquadrangleGraph hP hT c hdeg F h0 hfull u.2 v.2
      exact ⟨p⟩⟩
  have hediam4 : (Γ.induce S).ediam = 4 := by
    refine le_antisymm ?_ ?_
    · rw [SimpleGraph.ediam_le_iff]
      intro u v
      have hreach : (Γ.induce S).Reachable u v := by
        obtain ⟨p, -⟩ := exists_walk_subquadrangleGraph hP hT c hdeg F h0 hfull u.2 v.2
        exact ⟨p⟩
      rw [← SimpleGraph.Reachable.coe_dist_eq_edist hreach]
      rw [dist_subquadrangleGraph hP hT c hdeg F h0 hfull u.2 v.2]
      exact_mod_cast hP.dist_le (by norm_num) u.1 v.1
    · have hreach : (Γ.induce S).Reachable ⟨F.x, hxS⟩ ⟨F.y, hyS⟩ := by
        obtain ⟨p, -⟩ := exists_walk_subquadrangleGraph hP hT c hdeg F h0 hfull hxS hyS
        exact ⟨p⟩
      have hdist : (Γ.induce S).dist ⟨F.x, hxS⟩ ⟨F.y, hyS⟩ = 4 := by
        rw [dist_subquadrangleGraph hP hT c hdeg F h0 hfull hxS hyS, F.hxy]
      have h := SimpleGraph.edist_le_ediam (G := Γ.induce S)
        (u := ⟨F.x, hxS⟩) (v := ⟨F.y, hyS⟩)
      rw [← SimpleGraph.Reachable.coe_dist_eq_edist hreach, hdist] at h
      exact h
  have hbip : (Γ.induce S).IsBipartite :=
    ⟨SimpleGraph.Coloring.mk (fun v : S => c v.1)
      (by
        intro u v h
        exact c.valid (SimpleGraph.induce_adj.mp h))⟩
  have hAS : F.A ∈ S := Or.inr ⟨F.color_A hP h0, F.full_A hP h0 hfull⟩
  have hBS : F.B ∈ S := Or.inr ⟨F.color_B hP h0, F.full_B hP h0 hfull⟩
  have hCS : F.C ∈ S := Or.inr ⟨F.color_C hP h0, F.full_C hP h0 hfull⟩
  have hDS : F.D ∈ S := Or.inr ⟨F.color_D hP h0, F.full_D hP h0 hfull⟩
  have hw1 : ∀ z ∈ (SimpleGraph.Walk.cons F.hxA
      (SimpleGraph.Walk.cons F.huA.symm
        (SimpleGraph.Walk.cons F.huB (SimpleGraph.Walk.cons F.hyB.symm
          SimpleGraph.Walk.nil)))).support, z ∈ S := by
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hxS
    · exact hAS
    · exact Or.inl F.hu
    · exact hBS
    · exact hyS
  have hw2 : ∀ z ∈ (SimpleGraph.Walk.cons F.hxD
      (SimpleGraph.Walk.cons F.hvD.symm
        (SimpleGraph.Walk.cons F.hvC (SimpleGraph.Walk.cons F.hyC.symm
          SimpleGraph.Walk.nil)))).support, z ∈ S := by
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hxS
    · exact hDS
    · exact Or.inl F.hv
    · exact hCS
    · exact hyS
  have lift : ∀ (w : Γ.Walk F.x F.y) (hw : ∀ z ∈ w.support, z ∈ S),
      (w.induce S hw).length = w.length := by
    intro w hw
    have hmap : ((w.induce S hw).map (Embedding.induce S).toHom).length =
        (w.induce S hw).length := SimpleGraph.Walk.length_map _ _
    rw [SimpleGraph.Walk.map_induce] at hmap
    exact hmap.symm
  let p1 : (Γ.induce S).Walk ⟨F.x, hxS⟩ ⟨F.y, hyS⟩ :=
    ((SimpleGraph.Walk.cons F.hxA
      (SimpleGraph.Walk.cons F.huA.symm
        (SimpleGraph.Walk.cons F.huB (SimpleGraph.Walk.cons F.hyB.symm
          SimpleGraph.Walk.nil)))).induce S hw1).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let p2 : (Γ.induce S).Walk ⟨F.x, hxS⟩ ⟨F.y, hyS⟩ :=
    ((SimpleGraph.Walk.cons F.hxD
      (SimpleGraph.Walk.cons F.hvD.symm
        (SimpleGraph.Walk.cons F.hvC (SimpleGraph.Walk.cons F.hyC.symm
          SimpleGraph.Walk.nil)))).induce S hw2).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hp1len : p1.length = 4 := by
    rw [show p1.length = _ from SimpleGraph.Walk.length_copy _ _ _]
    rw [lift]
    simp
  have hp2len : p2.length = 4 := by
    rw [show p2.length = _ from SimpleGraph.Walk.length_copy _ _ _]
    rw [lift]
    simp
  have hp1path : p1.IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    rw [dist_subquadrangleGraph hP hT c hdeg F h0 hfull hxS hyS, F.hxy]
    exact hp1len
  have hp2path : p2.IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    rw [dist_subquadrangleGraph hP hT c hdeg F h0 hfull hxS hyS, F.hxy]
    exact hp2len
  have hp1v : p1.getVert 1 = ⟨F.A, hAS⟩ := by
    apply Subtype.ext
    simp [p1]
  have hp2v : p2.getVert 1 = ⟨F.D, hDS⟩ := by
    apply Subtype.ext
    simp [p2]
  have hpne : p1 ≠ p2 := by
    intro h
    have hv : p1.getVert 1 = p2.getVert 1 := congrArg (fun p => p.getVert 1) h
    rw [hp1v, hp2v] at hv
    exact F.A_ne_D hP (congrArg Subtype.val hv)
  obtain ⟨z, -, -, cz, hcz, hczlen⟩ :=
    hp1path.exists_isCycle_length_le_add_of_ne hp2path hpne
  have hgirth_le : (Γ.induce S).girth ≤ 8 := by
    have h1 := hcz.girth_le_length
    have h2 : cz.length ≤ p1.length + p2.length := hczlen
    omega
  have hnotAcyc : ¬ (Γ.induce S).IsAcyclic := fun h => h cz hcz
  obtain ⟨z', w, hwcycle, hwlen⟩ :=
    (SimpleGraph.exists_girth_eq_length (G := Γ.induce S)).mpr hnotAcyc
  have hgirth_ge : 8 ≤ (Γ.induce S).girth := by
    have hmapcycle : (w.map (Embedding.induce (G := Γ) S).toHom).IsCycle :=
      hwcycle.map (Embedding.induce (G := Γ) S).injective
    have hle := hmapcycle.girth_le_length
    rw [SimpleGraph.Walk.length_map] at hle
    have hg : Γ.girth = 8 := by simpa using hP.girth_eq
    rw [hg] at hle
    rwa [← hwlen] at hle
  refine ⟨hconn, hbip, ?_, ?_⟩
  · show (Γ.induce S).diam = 4
    simp [SimpleGraph.diam, hediam4]
  · show (Γ.induce S).girth = 8
    exact le_antisymm hgirth_le hgirth_ge


theorem exists_fullSubquadrangle_structure (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {P' : Set V} (h0 : ∀ x ∈ P', c x = 0)
    (hfull : ∀ L, c L = 1 → 2 ≤ (Γ.neighborSet L ∩ P').ncard →
      Γ.neighborSet L ⊆ P')
    (hquad : ∃ x ∈ P', ∃ y ∈ P', Γ.dist x y = 4 ∧
      2 ≤ (traceSet Γ x y ∩ P').ncard) :
    ∃ t' : ℕ, 1 ≤ t' ∧ IsFullSubquadrangle c P' t' ∧
      P'.ncard = (s + 1) * (s * t' + 1) ∧
      IsGeneralizedPolygon
        (Γ.induce (P' ∪ {L | c L = 1 ∧ Γ.neighborSet L ⊆ P'})) 4 := by
  obtain ⟨t', ht', hF⟩ := exists_isFullSubquadrangle hP hT c hdeg h0 hfull hquad
  refine ⟨t', ht', hF, ncard_of_isFullSubquadrangle hP hT c hdeg hF, ?_⟩
  have h := isGeneralizedPolygon_subquadrangleGraph hP hT c hdeg hF
  change IsGeneralizedPolygon (Γ.induce (P' ∪ subquadrangleLines Γ c P')) 4
  exact h

end Recognition

end CFSG.Geometry.GeneralizedQuadrangles
