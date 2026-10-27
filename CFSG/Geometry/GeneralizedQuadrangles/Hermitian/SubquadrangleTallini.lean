module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Subquadrangles
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Triads
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Varieties2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem mem_P'_of_subquadrangleColoring_eq_zero {P' : Set V}
    {v : subquadrangleSet Γ c P'} (hv : subquadrangleColoring c P' v = 0) : v.1 ∈ P' := by
  rcases mem_subquadrangleSet.mp v.2 with h | h
  · exact h
  · rw [subquadrangleColoring_apply, (mem_subquadrangleLines.mp h).1] at hv
    exact absurd hv (by decide)

theorem ptPerp_subquadrangle (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) (X : Set (subquadrangleSet Γ c P')) :
    Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') X = ptPerp Γ c (Subtype.val '' X) ∩ P' := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ptPerp] at hw
    refine ⟨?_, mem_P'_of_subquadrangleColoring_eq_zero hw.1⟩
    rw [mem_ptPerp]
    refine ⟨hw.1, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hle := hw.2 x hx
    rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF w.2 x.2]
      at hle
  · rintro ⟨hz, hzP⟩
    rw [mem_ptPerp] at hz
    refine ⟨⟨z, mem_subquadrangleSet.mpr (Or.inl hzP)⟩, ?_, rfl⟩
    rw [mem_ptPerp]
    refine ⟨hz.1, fun x hx => ?_⟩
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF _ x.2]
    exact hz.2 x.1 ⟨x, hx, rfl⟩

theorem spanSet_subquadrangle (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x y : subquadrangleSet Γ c P'}
    (hx : subquadrangleColoring c P' x = 0) (hxy : Γ.dist x.1 y.1 = 4) :
    Subtype.val '' spanSet (Γ.induce (subquadrangleSet Γ c P')) x y = spanSet Γ x.1 y.1 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  have hxy' : (Γ.induce (subquadrangleSet Γ c P')).dist x y = 4 := by
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF x.2 y.2, hxy]
  have hxP : x.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hx
  have hy0 : c y.1 = 0 := by
    have h := (hP.eq_iff_even_dist c y.1 x.1).2 (by
      rw [SimpleGraph.dist_comm, hxy]; exact ⟨2, rfl⟩)
    rw [h, hF.1 x.1 hxP]
  have hyP : y.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero (by
    rw [subquadrangleColoring_apply]; exact hy0)
  have hsub : spanSet Γ x.1 y.1 ⊆
      Subtype.val '' spanSet (Γ.induce (subquadrangleSet Γ c P')) x y := by
    intro z hz
    have hzP : z ∈ P' := spanSet_subset_of_isFullSubquadrangle hΓ hF hxP hyP hxy hz
    refine ⟨⟨z, mem_subquadrangleSet.mpr (Or.inl hzP)⟩, ?_, rfl⟩
    rw [mem_spanSet]
    intro w hw
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF _ w.2]
    apply hz
    exact ⟨by
      have h := hw.1
      rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF x.2 w.2] at h,
      by
      have h := hw.2
      rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF y.2 w.2] at h⟩
  have htrpos : 0 < (traceSet (Γ.induce (subquadrangleSet Γ c P')) x y).ncard := by
    rw [ncard_trace hP' hxy', degree_subquadrangleGraph hΓ hF x, if_pos hx]
    omega
  obtain ⟨w, hw⟩ := (Set.ncard_pos (s := traceSet (Γ.induce (subquadrangleSet Γ c P'))
    x y)).mp htrpos
  have hw0 : subquadrangleColoring c P' w = 0 :=
    color_eq_zero_of_dist_eq_two hP' hx hw.1
  have hw2 : ∀ z ∈ spanSet (Γ.induce (subquadrangleSet Γ c P')) x y,
      (Γ.induce (subquadrangleSet Γ c P')).dist z w = 2 :=
    fun z hz => dist_eq_two_of_mem_span_of_mem_trace hP' hT' hxy' hz hw
  let f : subquadrangleSet Γ c P' → subquadrangleSet Γ c P' := fun z =>
    if h : z ∈ spanSet (Γ.induce (subquadrangleSet Γ c P')) x y
      then commonNeighbor hP' (hw2 z h) else w
  have hfmap : ∀ z ∈ spanSet (Γ.induce (subquadrangleSet Γ c P')) x y,
      f z ∈ (Γ.induce (subquadrangleSet Γ c P')).neighborSet w := by
    intro z hz
    rw [mem_neighborSet]
    simp only [f, dif_pos hz]
    exact commonNeighbor_adj_right hP' (hw2 z hz)
  have hfinj : Set.InjOn f (spanSet (Γ.induce (subquadrangleSet Γ c P')) x y) := by
    intro z hz z' hz' heq
    have hzL : (Γ.induce (subquadrangleSet Γ c P')).Adj (f z) z := by
      simp only [f, dif_pos hz]
      exact (commonNeighbor_adj_left hP' (hw2 z hz)).symm
    have hz'L : (Γ.induce (subquadrangleSet Γ c P')).Adj (f z) z' := by
      rw [heq]
      simp only [f, dif_pos hz']
      exact (commonNeighbor_adj_left hP' (hw2 z' hz')).symm
    have hle1 := ncard_spanSet_inter_neighborSet_le_one hP' hT' hxy' (f z)
    exact (Set.ncard_le_one (s := spanSet (Γ.induce (subquadrangleSet Γ c P')) x y ∩
      (Γ.induce (subquadrangleSet Γ c P')).neighborSet (f z))).mp hle1 z ⟨hz, hzL⟩
      z' ⟨hz', hz'L⟩
  have hcardle : (spanSet (Γ.induce (subquadrangleSet Γ c P')) x y).ncard ≤ q + 1 := by
    rw [← hfinj.ncard_image]
    calc (f '' spanSet (Γ.induce (subquadrangleSet Γ c P')) x y).ncard
        ≤ ((Γ.induce (subquadrangleSet Γ c P')).neighborSet w).ncard :=
          Set.ncard_le_ncard (by rintro z ⟨z0, hz0, rfl⟩; exact hfmap z0 hz0)
      _ = (Γ.induce (subquadrangleSet Γ c P')).degree w :=
          ncard_neighborSet (Γ.induce (subquadrangleSet Γ c P')) w
      _ = q + 1 := by rw [degree_subquadrangleGraph hΓ hF w, if_pos hw0]
  have heq : spanSet Γ x.1 y.1 =
      Subtype.val '' spanSet (Γ.induce (subquadrangleSet Γ c P')) x y := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [Set.ncard_image_of_injective _ Subtype.val_injective,
      hΓ.span x.1 y.1 (hF.1 x.1 hxP) hxy]
    exact hcardle
  exact heq.symm

theorem isRegularVertex_subquadrangle (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) (x : subquadrangleSet Γ c P')
    (hx : subquadrangleColoring c P' x = 0) :
    IsRegularVertex (Γ.induce (subquadrangleSet Γ c P')) x := by
  classical
  intro y hxy'
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hxy : Γ.dist x.1 y.1 = 4 := by
    have h := hxy'
    rwa [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF x.2 y.2]
      at h
  rw [degree_subquadrangleGraph hΓ hF x, if_pos hx]
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
    spanSet_subquadrangle hΓ hF hx hxy]
  exact hΓ.span x.1 y.1 (hF.1 x.1 (mem_P'_of_subquadrangleColoring_eq_zero hx)) hxy

theorem starLine_subquadrangle_of_dist_four (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x y : subquadrangleSet Γ c P'}
    (hx : subquadrangleColoring c P' x = 0) (hxy : Γ.dist x.1 y.1 = 4) :
    Subtype.val '' starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') x y = spanSet Γ x.1 y.1 := by
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  have hxy' : (Γ.induce (subquadrangleSet Γ c P')).dist x y = 4 := by
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF x.2 y.2, hxy]
  rw [starLine_eq_spanSet hP' hT' (subquadrangleColoring c P') hx hxy']
  exact spanSet_subquadrangle hΓ hF hx hxy

theorem starLine_subquadrangle_of_dist_two (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x y : subquadrangleSet Γ c P'}
    (hx : subquadrangleColoring c P' x = 0) (hxy : Γ.dist x.1 y.1 = 2) :
    Subtype.val '' starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') x y =
      Γ.neighborSet (commonNeighbor hΓ.gp hxy) ∩ P' := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  have hxy' : (Γ.induce (subquadrangleSet Γ c P')).dist x y = 2 := by
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF x.2 y.2, hxy]
  have hx0 : c x.1 = 0 := by rwa [subquadrangleColoring_apply] at hx
  have hxP : x.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hx
  have hy0 : c y.1 = 0 := color_eq_zero_of_dist_eq_two hP hx0 hxy
  have hyP : y.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero (by
    rw [subquadrangleColoring_apply]; exact hy0)
  have hxyne : x.1 ≠ y.1 := by
    intro h
    rw [h] at hxy
    simp at hxy
  let L := commonNeighbor hP hxy
  have hLx : Γ.Adj x.1 L := commonNeighbor_adj_left hP hxy
  have hLy : Γ.Adj y.1 L := commonNeighbor_adj_right hP hxy
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hx0 hLx
  have hfull : Γ.neighborSet L ⊆ P' := by
    apply hF.2.1 L hL1
    have h2 : 1 < (Γ.neighborSet L ∩ P').ncard := by
      rw [Set.one_lt_ncard]
      exact ⟨x.1, ⟨hLx.symm, hxP⟩, y.1, ⟨hLy.symm, hyP⟩, hxyne⟩
    omega
  have hLS : L ∈ subquadrangleSet Γ c P' :=
    mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mpr ⟨hL1, hfull⟩))
  have hcn : commonNeighbor hP' hxy' = (⟨L, hLS⟩ : subquadrangleSet Γ c P') := by
    apply Subtype.ext
    have h1 : Γ.Adj x.1 (commonNeighbor hP' hxy').1 :=
      SimpleGraph.induce_adj.mp (commonNeighbor_adj_left hP' hxy')
    have h2 : Γ.Adj y.1 (commonNeighbor hP' hxy').1 :=
      SimpleGraph.induce_adj.mp (commonNeighbor_adj_right hP' hxy')
    exact (existsUnique_commonNeighbor hP hxy).unique ⟨h1, h2⟩ ⟨hLx, hLy⟩
  rw [starLine_eq_neighborSet hP' hT' (subquadrangleColoring c P') hx hxy', hcn]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : Γ.Adj L w.1 := SimpleGraph.induce_adj.mp hw
    exact ⟨hw', hfull hw'⟩
  · rintro ⟨hzL, hzP⟩
    exact ⟨⟨z, mem_subquadrangleSet.mpr (Or.inl hzP)⟩, SimpleGraph.induce_adj.mpr hzL, rfl⟩



@[expose] def subquadrangleTrace (Γ : SimpleGraph V) (c : Γ.Coloring (Fin 2)) (P' : Set V)
    (u v : V) : Set (subquadrangleSet Γ c P') :=
  {w | w.1 ∈ traceSet Γ u v}

theorem traceSet_subset_of_isFullSubquadrangle (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {u v : V} (hu : c u = 0) (huv : Γ.dist u v = 4)
    {x y z : V} (hx : x ∈ traceSet Γ u v ∩ P') (hy : y ∈ traceSet Γ u v ∩ P')
    (hz : z ∈ traceSet Γ u v ∩ P') (hxy : x ≠ y) (hz' : z ∉ spanSet Γ x y) :
    traceSet Γ u v ⊆ P' := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  have hdeg' : ∀ w : subquadrangleSet Γ c P',
      (Γ.induce (subquadrangleSet Γ c P')).degree w =
        if subquadrangleColoring c P' w = 0 then q + 1 else q ^ 2 + 1 :=
    fun w => degree_subquadrangleGraph hΓ hF w
  have hreg' : ∀ w : subquadrangleSet Γ c P', subquadrangleColoring c P' w = 0 →
      IsRegularVertex (Γ.induce (subquadrangleSet Γ c P')) w :=
    fun w hw => isRegularVertex_subquadrangle hΓ hF w hw
  have hxT : x ∈ traceSet Γ u v := hx.1
  have hyT : y ∈ traceSet Γ u v := hy.1
  have hzT : z ∈ traceSet Γ u v := hz.1
  have hxP : x ∈ P' := hx.2
  have hyP : y ∈ P' := hy.2
  have hzP : z ∈ P' := hz.2
  have hx0 : c x = 0 := color_eq_zero_of_dist_eq_two hP hu hxT.1
  have hy0 : c y = 0 := color_eq_zero_of_dist_eq_two hP hu hyT.1
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hu hzT.1
  have hv0 : c v = 0 := by
    have h := (hP.eq_iff_even_dist c v u).2 (by
      rw [SimpleGraph.dist_comm, huv]; exact ⟨2, rfl⟩)
    rwa [h, hu]
  have hxy4 : Γ.dist x y = 4 := dist_eq_four_of_mem_trace hP huv hxT hyT hxy
  have hmemP : ∀ a : subquadrangleSet Γ c P', a.1 ∈ traceSet Γ u v → a.1 ∈ P' := by
    intro a ha
    rcases mem_subquadrangleSet.mp a.2 with h | h
    · exact h
    · have h0 : c a.1 = 0 := color_eq_zero_of_dist_eq_two hP hu ha.1
      rw [(mem_subquadrangleLines.mp h).1] at h0
      exact absurd h0 (by decide)
  let x' : subquadrangleSet Γ c P' := ⟨x, mem_subquadrangleSet.mpr (Or.inl hxP)⟩
  let y' : subquadrangleSet Γ c P' := ⟨y, mem_subquadrangleSet.mpr (Or.inl hyP)⟩
  let z' : subquadrangleSet Γ c P' := ⟨z, mem_subquadrangleSet.mpr (Or.inl hzP)⟩
  have hx'0 : subquadrangleColoring c P' x' = 0 := by
    rw [subquadrangleColoring_apply]; exact hx0
  have hx'y' : x' ≠ y' := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hnc : ¬ IsStarCollinear (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') x' y' z' := by
    rintro ⟨M, hM, hxM, hyM, hzM⟩
    have hMxy : M = starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') x' y' :=
      starLine_eq_of_isStarLine_of_mem hP' hT' hM hxM hyM hx'y'
    have hzimg : z ∈ Subtype.val '' starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') x' y' := by
      refine ⟨z', ?_, rfl⟩
      rw [← hMxy]
      exact hzM
    rw [starLine_subquadrangle_of_dist_four hΓ hF hx'0 hxy4] at hzimg
    exact hz' hzimg
  have hlin : IsLinearVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') (subquadrangleTrace Γ c P' u v) := by
    refine ⟨?_, ?_⟩
    · intro a ha
      have h0 : c a.1 = 0 := color_eq_zero_of_dist_eq_two hP hu ha.1
      rw [subquadrangleColoring_apply]
      exact h0
    · intro a ha b hb hab w hw
      have haT : a.1 ∈ traceSet Γ u v := ha
      have hbT : b.1 ∈ traceSet Γ u v := hb
      have ha0 : c a.1 = 0 := color_eq_zero_of_dist_eq_two hP hu haT.1
      have hab4 : Γ.dist a.1 b.1 = 4 :=
        dist_eq_four_of_mem_trace hP huv haT hbT (fun h => hab (Subtype.ext h))
      have ha'0 : subquadrangleColoring c P' a = 0 := by
        rw [subquadrangleColoring_apply]; exact ha0
      have hwimg : w.1 ∈ Subtype.val '' starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') a b := ⟨w, hw, rfl⟩
      rw [starLine_subquadrangle_of_dist_four hΓ hF ha'0 hab4] at hwimg
      have hu_ab : u ∈ traceSet Γ a.1 b.1 :=
        ⟨by rw [SimpleGraph.dist_comm]; exact haT.1,
          by rw [SimpleGraph.dist_comm]; exact hbT.1⟩
      have hv_ab : v ∈ traceSet Γ a.1 b.1 :=
        ⟨by rw [SimpleGraph.dist_comm]; exact haT.2,
          by rw [SimpleGraph.dist_comm]; exact hbT.2⟩
      have hw0 : c w.1 = 0 := (color_eq_of_mem_span hP hT c hab4 hwimg).trans ha0
      have hleu : Γ.dist u w.1 ≤ 2 := by
        have := hwimg u hu_ab
        rwa [SimpleGraph.dist_comm] at this
      have hlev : Γ.dist v w.1 ≤ 2 := by
        have := hwimg v hv_ab
        rwa [SimpleGraph.dist_comm] at this
      refine ⟨?_, ?_⟩
      · have hne : Γ.dist u w.1 ≠ 0 := by
          intro h0
          have hwu : w.1 = u := (hP.connected.dist_eq_zero_iff).mp (by
            rwa [SimpleGraph.dist_comm])
          exact not_mem_spanSet_of_mem_traceSet hP hT hab4 hu_ab (hwu ▸ hwimg)
        have heven : Even (Γ.dist u w.1) :=
          (hP.eq_iff_even_dist c u w.1).1 (by rw [hu, hw0])
        obtain ⟨k, hk⟩ := heven
        omega
      · have hne : Γ.dist v w.1 ≠ 0 := by
          intro h0
          have hwv : w.1 = v := (hP.connected.dist_eq_zero_iff).mp (by
            rwa [SimpleGraph.dist_comm])
          exact not_mem_spanSet_of_mem_traceSet hP hT hab4 hv_ab (hwv ▸ hwimg)
        have heven : Even (Γ.dist v w.1) :=
          (hP.eq_iff_even_dist c v w.1).1 (by rw [hv0, hw0])
        obtain ⟨k, hk⟩ := heven
        omega
  have hpair : ∀ a ∈ subquadrangleTrace Γ c P' u v, ∀ b ∈ subquadrangleTrace Γ c P' u v, a ≠ b →
      (Γ.induce (subquadrangleSet Γ c P')).dist a b = 4 := by
    intro a ha b hb hab
    have hab4 : Γ.dist a.1 b.1 = 4 :=
      dist_eq_four_of_mem_trace hP huv ha hb (fun h => hab (Subtype.ext h))
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF a.2 b.2, hab4]
  have h3 : ∃ a ∈ subquadrangleTrace Γ c P' u v, ∃ b ∈ subquadrangleTrace Γ c P' u v,
      ∃ d ∈ subquadrangleTrace Γ c P' u v,
        ¬ IsStarCollinear (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') a b d :=
    ⟨x', hxT, y', hyT, z', hzT, hnc⟩
  have hOvoid : IsOvoid (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') (subquadrangleTrace Γ c P' u v) :=
    isOvoid_of_isLinearVariety hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q)
      hdeg' hreg' hlin hpair h3
  have hXcard : (subquadrangleTrace Γ c P' u v).ncard = q ^ 2 * q + 1 :=
    ncard_of_isOvoid hP' hT' (subquadrangleColoring c P') (s := q ^ 2) (t := q) hdeg' hOvoid
  have hvalX : Subtype.val '' subquadrangleTrace Γ c P' u v = traceSet Γ u v ∩ P' := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, hmemP a ha⟩
    · rintro ⟨hwT, hwP⟩
      exact ⟨⟨w, mem_subquadrangleSet.mpr (Or.inl hwP)⟩, hwT, rfl⟩
  have hcardTP : (traceSet Γ u v ∩ P').ncard = q ^ 3 + 1 := by
    rw [← hvalX, Set.ncard_image_of_injective _ Subtype.val_injective, hXcard]
    ring
  have hTcard : (traceSet Γ u v).ncard = q ^ 3 + 1 := by
    rw [ncard_trace hP huv, hΓ.deg u, if_pos hu]
  have heq : traceSet Γ u v ∩ P' = traceSet Γ u v :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hcardTP, hTcard])
  intro w hw
  have : w ∈ traceSet Γ u v ∩ P' := by rw [heq]; exact hw
  exact this.2

theorem val_image_subquadrangleTrace (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {u v : V} (hTP : traceSet Γ u v ⊆ P') :
    Subtype.val '' subquadrangleTrace Γ c P' u v = traceSet Γ u v := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hw
    exact ⟨⟨w, mem_subquadrangleSet.mpr (Or.inl (hTP hw))⟩, hw, rfl⟩

theorem isLinearVariety_subquadrangleTrace (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {u v : V} (hu : c u = 0) (huv : Γ.dist u v = 4) :
    IsLinearVariety (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') (subquadrangleTrace Γ c P' u v) := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  refine ⟨?_, ?_⟩
  · intro a ha
    have h0 : c a.1 = 0 := color_eq_zero_of_dist_eq_two hP hu ha.1
    rw [subquadrangleColoring_apply]
    exact h0
  · intro a ha b hb hab w hw
    have haT : a.1 ∈ traceSet Γ u v := ha
    have hbT : b.1 ∈ traceSet Γ u v := hb
    have ha0 : c a.1 = 0 := color_eq_zero_of_dist_eq_two hP hu haT.1
    have hab4 : Γ.dist a.1 b.1 = 4 :=
      dist_eq_four_of_mem_trace hP huv haT hbT (fun h => hab (Subtype.ext h))
    have ha'0 : subquadrangleColoring c P' a = 0 := by
      rw [subquadrangleColoring_apply]; exact ha0
    have hwimg : w.1 ∈ Subtype.val '' starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') a b := ⟨w, hw, rfl⟩
    rw [starLine_subquadrangle_of_dist_four hΓ hF ha'0 hab4] at hwimg
    have hu_ab : u ∈ traceSet Γ a.1 b.1 :=
      ⟨by rw [SimpleGraph.dist_comm]; exact haT.1,
        by rw [SimpleGraph.dist_comm]; exact hbT.1⟩
    have hv_ab : v ∈ traceSet Γ a.1 b.1 :=
      ⟨by rw [SimpleGraph.dist_comm]; exact haT.2,
        by rw [SimpleGraph.dist_comm]; exact hbT.2⟩
    have hw0 : c w.1 = 0 := (color_eq_of_mem_span hP hT c hab4 hwimg).trans ha0
    have hleu : Γ.dist u w.1 ≤ 2 := by
      have := hwimg u hu_ab
      rwa [SimpleGraph.dist_comm] at this
    have hlev : Γ.dist v w.1 ≤ 2 := by
      have := hwimg v hv_ab
      rwa [SimpleGraph.dist_comm] at this
    have hv0 : c v = 0 := by
      have h := (hP.eq_iff_even_dist c v u).2 (by
        rw [SimpleGraph.dist_comm, huv]; exact ⟨2, rfl⟩)
      rwa [h, hu]
    refine ⟨?_, ?_⟩
    · have hne : Γ.dist u w.1 ≠ 0 := by
        intro h0
        have hwu : w.1 = u := (hP.connected.dist_eq_zero_iff).mp (by
          rwa [SimpleGraph.dist_comm])
        exact not_mem_spanSet_of_mem_traceSet hP hT hab4 hu_ab (hwu ▸ hwimg)
      have heven : Even (Γ.dist u w.1) :=
        (hP.eq_iff_even_dist c u w.1).1 (by rw [hu, hw0])
      obtain ⟨k, hk⟩ := heven
      omega
    · have hne : Γ.dist v w.1 ≠ 0 := by
        intro h0
        have hwv : w.1 = v := (hP.connected.dist_eq_zero_iff).mp (by
          rwa [SimpleGraph.dist_comm])
        exact not_mem_spanSet_of_mem_traceSet hP hT hab4 hv_ab (hwv ▸ hwimg)
      have heven : Even (Γ.dist v w.1) :=
        (hP.eq_iff_even_dist c v w.1).1 (by rw [hv0, hw0])
      obtain ⟨k, hk⟩ := heven
      omega

theorem pairwise_subquadrangleTrace (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {u v : V} (huv : Γ.dist u v = 4) :
    ∀ a ∈ subquadrangleTrace Γ c P' u v, ∀ b ∈ subquadrangleTrace Γ c P' u v, a ≠ b →
      (Γ.induce (subquadrangleSet Γ c P')).dist a b = 4 := by
  intro a ha b hb hab
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hab4 : Γ.dist a.1 b.1 = 4 :=
    dist_eq_four_of_mem_trace hP huv ha hb (fun h => hab (Subtype.ext h))
  rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF a.2 b.2, hab4]

private theorem exists_mem_P'_not_mem_trace (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {u v : V} (hu : c u = 0) (huv : Γ.dist u v = 4) :
    ∃ w ∈ P', w ∉ traceSet Γ u v := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  by_contra h
  push Not at h
  have hPcard : P'.ncard = (q ^ 2 + 1) * (q ^ 2 * q + 1) :=
    ncard_of_isFullSubquadrangle hP hΓ.thick c hΓ.deg hF
  have hTcard : (traceSet Γ u v).ncard = q ^ 3 + 1 := by
    rw [ncard_trace hP huv, hΓ.deg u, if_pos hu]
  have hle : P'.ncard ≤ (traceSet Γ u v).ncard := Set.ncard_le_ncard (fun w hw => h w hw)
  rw [hPcard, hTcard] at hle
  have h2 : 2 ≤ q ^ 2 + 1 := by nlinarith [hΓ.two_le]
  have h3 : 0 < q ^ 3 + 1 := by positivity
  have h4 : 2 * (q ^ 3 + 1) ≤ (q ^ 2 + 1) * (q ^ 2 * q + 1) := Nat.mul_le_mul_right _ h2
  omega

theorem isStarPlane_subquadrangleTrace (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {u v : V} (hu : c u = 0) (huv : Γ.dist u v = 4)
    (hTP : traceSet Γ u v ⊆ P') {x y z : subquadrangleSet Γ c P'}
    (hxT : x.1 ∈ traceSet Γ u v) (hyT : y.1 ∈ traceSet Γ u v)
    (hzT : z.1 ∈ traceSet Γ u v)
    (hnc : ¬ IsStarCollinear (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') x y z) :
    IsStarPlane (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') (subquadrangleTrace Γ c P' u v) := by
  refine ⟨⟨isLinearVariety_subquadrangleTrace hΓ hF hu huv, ?_⟩, x, hxT, y, hyT, z, hzT, hnc⟩
  obtain ⟨w, hwP, hwT⟩ := exists_mem_P'_not_mem_trace hΓ hF hu huv
  exact ⟨⟨w, mem_subquadrangleSet.mpr (Or.inl hwP)⟩,
    by rw [subquadrangleColoring_apply]; exact hF.1 w hwP, hwT⟩

private theorem exists_other_point (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x : subquadrangleSet Γ c P'}
    (hx : subquadrangleColoring c P' x = 0) :
    ∃ w : subquadrangleSet Γ c P', subquadrangleColoring c P' w = 0 ∧ w ≠ x := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF
  have hdegx : (Γ.induce (subquadrangleSet Γ c P')).degree x = q + 1 := by
    rw [degree_subquadrangleGraph hΓ hF x, if_pos hx]
  have hpos : 0 < ((Γ.induce (subquadrangleSet Γ c P')).neighborSet x).ncard := by
    rw [ncard_neighborSet, hdegx]
    omega
  obtain ⟨L, hxL⟩ := (Set.ncard_pos (s := (Γ.induce (subquadrangleSet Γ c P')).neighborSet
    x)).mp hpos
  have hL1 : subquadrangleColoring c P' L = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hx hxL
  have hdegL : (Γ.induce (subquadrangleSet Γ c P')).degree L = q ^ 2 + 1 := by
    rw [degree_subquadrangleGraph hΓ hF L, if_neg (by rw [hL1]; decide)]
  have hpos2 : 1 < ((Γ.induce (subquadrangleSet Γ c P')).neighborSet L).ncard := by
    rw [ncard_neighborSet, hdegL]
    nlinarith [hΓ.two_le]
  obtain ⟨w, hwL, hwx⟩ := Set.exists_ne_of_one_lt_ncard hpos2 x
  have hw0 : subquadrangleColoring c P' w = 0 := by
    have hne := (subquadrangleColoring c P').valid hwL
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (subquadrangleColoring c P' w) with h | h
    · exact h
    · exact absurd (hL1.trans h.symm) hne
  exact ⟨w, hw0, hwx⟩

private theorem exists_ptPerp_of_dist_two (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x y z : subquadrangleSet Γ c P'}
    (hx : subquadrangleColoring c P' x = 0) (hy : subquadrangleColoring c P' y = 0)
    (hz : subquadrangleColoring c P' z = 0) (hxy : Γ.dist x.1 y.1 = 2)
    (hnc : ¬ IsStarCollinear (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') x y z) :
    ∃ u : subquadrangleSet Γ c P', subquadrangleColoring c P' u = 0 ∧
      x ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') {u} ∧
      y ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') {u} ∧
      z ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') {u} := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF hΓ.two_le
  have hxy' : (Γ.induce (subquadrangleSet Γ c P')).dist x y = 2 := by
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF x.2 y.2, hxy]
  have hx0 : c x.1 = 0 := by rwa [subquadrangleColoring_apply] at hx
  have hxP : x.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hx
  have hyP : y.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hy
  have hz0 : c z.1 = 0 := by rwa [subquadrangleColoring_apply] at hz
  have hzP : z.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hz
  have hxyne : x.1 ≠ y.1 := by
    intro h; rw [h] at hxy; simp at hxy
  let L := commonNeighbor hP hxy
  have hLx : Γ.Adj x.1 L := commonNeighbor_adj_left hP hxy
  have hLy : Γ.Adj y.1 L := commonNeighbor_adj_right hP hxy
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hx0 hLx
  have hfull : Γ.neighborSet L ⊆ P' := by
    apply hF.2.1 L hL1
    have h2 : 1 < (Γ.neighborSet L ∩ P').ncard := by
      rw [Set.one_lt_ncard]
      exact ⟨x.1, ⟨hLx.symm, hxP⟩, y.1, ⟨hLy.symm, hyP⟩, hxyne⟩
    omega
  have hLnot : ¬ Γ.Adj L z.1 := by
    intro hLz
    have hzL : z ∈ (Γ.induce (subquadrangleSet Γ c P')).neighborSet
        (⟨L, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mpr
          ⟨hL1, hfull⟩))⟩ : subquadrangleSet Γ c P') :=
      SimpleGraph.induce_adj.mpr hLz
    have hzstar : z ∈ starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') x y := by
      have hzimg : z.1 ∈ Subtype.val '' starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') x y := by
        rw [starLine_subquadrangle_of_dist_two hΓ hF hx hxy]
        exact ⟨hLz, hzP⟩
      obtain ⟨a, ha, hav⟩ := hzimg
      have haz : a = z := Subtype.ext hav
      rwa [haz] at ha
    exact hnc ⟨starLine (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') x y,
      isStarLine_starLine hx hy (fun h => hxyne (congrArg Subtype.val h)),
      mem_starLine_left hx, mem_starLine_right hy, hzstar⟩
  have hdist3 : Γ.dist z.1 L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hLnot h.symm)
      (by rw [hz0, hL1]; decide)
  let u := proj hP hdist3
  have hLu : Γ.Adj L u := proj_adj hP hdist3
  have hzu : Γ.dist z.1 u = 2 := proj_dist hP hdist3
  have huP : u ∈ P' := hfull hLu
  have hu0 : c u = 0 := by
    have hne := c.valid hLu
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c u) with h | h
    · exact h
    · exact absurd (hL1.trans h.symm) hne
  let u' : subquadrangleSet Γ c P' := ⟨u, mem_subquadrangleSet.mpr (Or.inl huP)⟩
  have hu'0 : subquadrangleColoring c P' u' = 0 := by
    rw [subquadrangleColoring_apply]; exact hu0
  have hxu : Γ.dist x.1 u ≤ 2 := by
    have htri := hP.connected.dist_triangle (u := x.1) (v := L) (w := u)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hLx,
      SimpleGraph.dist_eq_one_iff_adj.mpr hLu] at htri
    omega
  have hyu : Γ.dist y.1 u ≤ 2 := by
    have htri := hP.connected.dist_triangle (u := y.1) (v := L) (w := u)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hLy,
      SimpleGraph.dist_eq_one_iff_adj.mpr hLu] at htri
    omega
  refine ⟨u', hu'0, ?_, ?_, ?_⟩
  · rw [mem_ptPerp]
    refine ⟨hx, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF x.2 u'.2]
    exact hxu
  · rw [mem_ptPerp]
    refine ⟨hy, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF y.2 u'.2]
    exact hyu
  · rw [mem_ptPerp]
    refine ⟨hz, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF z.2 u'.2]
    exact le_of_eq hzu

theorem exists_ptPerp_of_mem_clSet (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x y z : subquadrangleSet Γ c P'}
    (hx : subquadrangleColoring c P' x = 0) (hy : subquadrangleColoring c P' y = 0)
    (hz : subquadrangleColoring c P' z = 0) (hxy : Γ.dist x.1 y.1 = 4)
    (hzcl : z.1 ∈ clSet Γ x.1 y.1) (hzspan : z.1 ∉ spanSet Γ x.1 y.1) :
    ∃ u : subquadrangleSet Γ c P', subquadrangleColoring c P' u = 0 ∧
      x ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') {u} ∧
      y ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') {u} ∧
      z ∈ ptPerp (Γ.induce (subquadrangleSet Γ c P')) (subquadrangleColoring c P') {u} := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hxP : x.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hx
  have hyP : y.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hy
  have hzP : z.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hz
  have hx0 : c x.1 = 0 := by rwa [subquadrangleColoring_apply] at hx
  have hy0 : c y.1 = 0 := by rwa [subquadrangleColoring_apply] at hy
  have hz0 : c z.1 = 0 := by rwa [subquadrangleColoring_apply] at hz
  obtain ⟨w, hwspan, hzwle⟩ := hzcl
  have hw0 : c w = 0 := (color_eq_of_mem_span hP hT c hxy hwspan).trans hx0
  have hwP : w ∈ P' := spanSet_subset_of_isFullSubquadrangle hΓ hF hxP hyP hxy hwspan
  have hzw_ne : z.1 ≠ w := by
    intro h; exact hzspan (h ▸ hwspan)
  have hzw2 : Γ.dist z.1 w = 2 := by
    have heven : Even (Γ.dist z.1 w) := (hP.eq_iff_even_dist c z.1 w).1 (by rw [hz0, hw0])
    have hne : Γ.dist z.1 w ≠ 0 := by
      intro h0
      exact hzw_ne ((hP.connected.dist_eq_zero_iff).mp h0)
    obtain ⟨k, hk⟩ := heven
    omega
  let L := commonNeighbor hP hzw2
  have hLz : Γ.Adj z.1 L := commonNeighbor_adj_left hP hzw2
  have hLw : Γ.Adj w L := commonNeighbor_adj_right hP hzw2
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hz0 hLz
  have hLfull : Γ.neighborSet L ⊆ P' := by
    apply hF.2.1 L hL1
    have h2 : 1 < (Γ.neighborSet L ∩ P').ncard := by
      rw [Set.one_lt_ncard]
      exact ⟨z.1, ⟨hLz.symm, hzP⟩, w, ⟨hLw.symm, hwP⟩, hzw_ne⟩
    omega
  let T : Set V := traceSet Γ x.1 y.1
  have hTcard : T.ncard = q ^ 3 + 1 := by
    rw [ncard_trace hP hxy, hΓ.deg x.1, if_pos hx0]
  have hwncard : (Γ.neighborSet w).ncard = q ^ 3 + 1 := by
    rw [ncard_neighborSet, hΓ.deg w, if_pos hw0]
  let φ : V → V := fun u =>
    if h : u ∈ T then
      commonNeighbor hP (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hwspan h)
    else w
  have hφmem : ∀ u ∈ T, φ u ∈ Γ.neighborSet w := by
    intro u hu
    rw [mem_neighborSet]
    simp only [φ, dif_pos hu]
    exact commonNeighbor_adj_left hP
      (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hwspan hu)
  have hφinj : Set.InjOn φ T := by
    intro u hu u' hu' heq
    have huL : Γ.Adj u (φ u) := by
      simp only [φ, dif_pos hu]
      exact commonNeighbor_adj_right hP
        (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hwspan hu)
    have hu'L : Γ.Adj u' (φ u) := by
      rw [heq]
      simp only [φ, dif_pos hu']
      exact commonNeighbor_adj_right hP
        (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hwspan hu')
    by_contra hne
    have h4 : Γ.dist u u' = 4 := dist_eq_four_of_mem_trace hP hxy hu hu' hne
    have h2 : Γ.dist u u' = 2 := dist_eq_two_of_adj_of_adj_of_ne hP huL hu'L.symm hne
    omega
  have himeq : φ '' T = Γ.neighborSet w := by
    refine Set.eq_of_subset_of_ncard_le (fun a ha => ?_) ?_
    · obtain ⟨u, hu, rfl⟩ := ha
      exact hφmem u hu
    · rw [hφinj.ncard_image, hTcard, hwncard]
  have hLmem : L ∈ φ '' T := by rw [himeq]; exact hLw
  obtain ⟨u, huT, hφu⟩ := hLmem
  have hLu : Γ.Adj L u := by
    have h := commonNeighbor_adj_right hP
      (dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hwspan huT)
    simp only [φ, dif_pos huT] at hφu
    rw [hφu] at h
    exact h.symm
  have huP : u ∈ P' := hLfull hLu
  have hu0 : c u = 0 := by
    have hne := c.valid hLu
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c u) with h | h
    · exact h
    · exact absurd (hL1.trans h.symm) hne
  let u' : subquadrangleSet Γ c P' := ⟨u, mem_subquadrangleSet.mpr (Or.inl huP)⟩
  have hu'0 : subquadrangleColoring c P' u' = 0 := by
    rw [subquadrangleColoring_apply]; exact hu0
  have hxu : Γ.dist x.1 u = 2 := huT.1
  have hyu : Γ.dist y.1 u = 2 := huT.2
  have hzu : Γ.dist z.1 u ≤ 2 := by
    have htri := hP.connected.dist_triangle (u := z.1) (v := L) (w := u)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hLz,
      SimpleGraph.dist_eq_one_iff_adj.mpr hLu] at htri
    omega
  refine ⟨u', hu'0, ?_, ?_, ?_⟩
  · rw [mem_ptPerp]
    refine ⟨hx, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF x.2 u'.2]
    exact le_of_eq hxu
  · rw [mem_ptPerp]
    refine ⟨hy, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF y.2 u'.2]
    exact le_of_eq hyu
  · rw [mem_ptPerp]
    refine ⟨hz, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [dist_subquadrangleGraph_of_isFullSubquadrangle hP hT c hΓ.deg hF z.2 u'.2]
    exact hzu

theorem exists_traceSet_of_not_mem_clSet (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x y z : subquadrangleSet Γ c P'}
    (hx : subquadrangleColoring c P' x = 0) (hy : subquadrangleColoring c P' y = 0)
    (hz : subquadrangleColoring c P' z = 0) (hxy : Γ.dist x.1 y.1 = 4)
    (hzcl : z.1 ∉ clSet Γ x.1 y.1) :
    ∃ u v : V, c u = 0 ∧ Γ.dist u v = 4 ∧ traceSet Γ u v ⊆ P' ∧
      x.1 ∈ traceSet Γ u v ∧ y.1 ∈ traceSet Γ u v ∧ z.1 ∈ traceSet Γ u v := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hx0 : c x.1 = 0 := by rwa [subquadrangleColoring_apply] at hx
  have hy0 : c y.1 = 0 := by rwa [subquadrangleColoring_apply] at hy
  have hz0 : c z.1 = 0 := by rwa [subquadrangleColoring_apply] at hz
  have hxP : x.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hx
  have hyP : y.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hy
  have hzP : z.1 ∈ P' := mem_P'_of_subquadrangleColoring_eq_zero hz
  have hzx : Γ.dist z.1 x.1 = 4 := by
    have hgt : 2 < Γ.dist z.1 x.1 := by
      by_contra h
      exact hzcl ⟨x.1, left_mem_spanSet hxy, by omega⟩
    have heven : Even (Γ.dist z.1 x.1) :=
      (hP.eq_iff_even_dist c z.1 x.1).1 (by rw [hz0, hx0])
    have hle : Γ.dist z.1 x.1 ≤ 4 := hP.dist_le (by norm_num) _ _
    obtain ⟨k, hk⟩ := heven
    omega
  have hzy : Γ.dist z.1 y.1 = 4 := by
    have hgt : 2 < Γ.dist z.1 y.1 := by
      by_contra h
      exact hzcl ⟨y.1, right_mem_spanSet hxy, by omega⟩
    have heven : Even (Γ.dist z.1 y.1) :=
      (hP.eq_iff_even_dist c z.1 y.1).1 (by rw [hz0, hy0])
    have hle : Γ.dist z.1 y.1 ≤ 4 := hP.dist_le (by norm_num) _ _
    obtain ⟨k, hk⟩ := heven
    omega
  have hc : (centreSet Γ x.1 y.1 z.1).ncard = q + 1 :=
    ncard_centreSet hΓ hx0 hxy (by rwa [SimpleGraph.dist_comm]) (by rwa [SimpleGraph.dist_comm])
      hzcl
  have h2 : 1 < (centreSet Γ x.1 y.1 z.1).ncard := by
    rw [hc]
    have hq := hΓ.two_le
    omega
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Set.one_lt_ncard (s := centreSet Γ x.1 y.1 z.1)).mp h2
  have huT : u ∈ traceSet Γ x.1 y.1 := hu.1
  have hzu : Γ.dist z.1 u = 2 := hu.2
  have hvT : v ∈ traceSet Γ x.1 y.1 := hv.1
  have hzv : Γ.dist z.1 v = 2 := hv.2
  have hu0 : c u = 0 := color_eq_zero_of_dist_eq_two hP hx0 huT.1
  have huv4 : Γ.dist u v = 4 := dist_eq_four_of_mem_trace hP hxy huT hvT huv
  have hx_uv : x.1 ∈ traceSet Γ u v :=
    ⟨by rw [SimpleGraph.dist_comm]; exact huT.1,
      by rw [SimpleGraph.dist_comm]; exact hvT.1⟩
  have hy_uv : y.1 ∈ traceSet Γ u v :=
    ⟨by rw [SimpleGraph.dist_comm]; exact huT.2,
      by rw [SimpleGraph.dist_comm]; exact hvT.2⟩
  have hz_uv : z.1 ∈ traceSet Γ u v :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hzu,
      by rw [SimpleGraph.dist_comm]; exact hzv⟩
  have hzsp : z.1 ∉ spanSet Γ x.1 y.1 := by
    intro h
    exact hzcl ⟨z.1, h, by simp⟩
  have hTP : traceSet Γ u v ⊆ P' :=
    traceSet_subset_of_isFullSubquadrangle hΓ hF hu0 huv4
      ⟨hx_uv, hxP⟩ ⟨hy_uv, hyP⟩ ⟨hz_uv, hzP⟩
      (by intro h; rw [h] at hxy; simp at hxy) hzsp
  exact ⟨u, v, hu0, huv4, hTP, hx_uv, hy_uv, hz_uv⟩

theorem talliniCondPrime_subquadrangle (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) :
    TalliniCondPrime (Γ.induce (subquadrangleSet Γ c P'))
      (subquadrangleColoring c P') := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P')) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hΓ.thick c hΓ.deg hF
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c P')) :=
    isThick_subquadrangleGraph hP hΓ.thick c hΓ.deg hF hΓ.two_le
  have hdeg' : ∀ w : subquadrangleSet Γ c P',
      (Γ.induce (subquadrangleSet Γ c P')).degree w =
        if subquadrangleColoring c P' w = 0 then q + 1 else q ^ 2 + 1 :=
    fun w => degree_subquadrangleGraph hΓ hF w
  intro x y z hx hy hz hnc
  have hxyne : x ≠ y := by
    intro hxy
    apply hnc
    by_cases hxz : x = z
    · subst hxz
      subst hxy
      obtain ⟨w, hw0, hwx⟩ := exists_other_point hΓ hF hx
      exact ⟨starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') x w,
        isStarLine_starLine hx hw0 hwx.symm, mem_starLine_left hx, mem_starLine_left hx,
        mem_starLine_left hx⟩
    · subst hxy
      exact ⟨starLine (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') x z,
        isStarLine_starLine hx hz hxz, mem_starLine_left hx, mem_starLine_left hx,
        mem_starLine_right hz⟩
  have hx0 : c x.1 = 0 := by rwa [subquadrangleColoring_apply] at hx
  have hy0 : c y.1 = 0 := by rwa [subquadrangleColoring_apply] at hy
  have hxyne' : x.1 ≠ y.1 := fun h => hxyne (Subtype.ext h)
  rcases dist_eq_two_or_four_of_color_zero hP hx0 hy0 hxyne' with hxy2 | hxy4
  · obtain ⟨u, hu0, hxu, hyu, hzu⟩ :=
      exists_ptPerp_of_dist_two hΓ hF hx hy hz hxy2 hnc
    exact ⟨ptPerp (Γ.induce (subquadrangleSet Γ c P'))
        (subquadrangleColoring c P') {u},
      isStarPlane_ptPerp_singleton hP' hT' (subquadrangleColoring c P')
        (s := q ^ 2) (t := q) hdeg' hu0, hxu, hyu, hzu⟩
  · by_cases hcl : z.1 ∈ clSet Γ x.1 y.1
    · have hzspan : z.1 ∉ spanSet Γ x.1 y.1 := by
        intro hzsp
        apply hnc
        have hzstar : z ∈ starLine (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') x y := by
          have hzimg : z.1 ∈ Subtype.val '' starLine (Γ.induce (subquadrangleSet Γ c P'))
              (subquadrangleColoring c P') x y := by
            rw [starLine_subquadrangle_of_dist_four hΓ hF hx hxy4]
            exact hzsp
          obtain ⟨a, ha, hav⟩ := hzimg
          have haz : a = z := Subtype.ext hav
          rwa [haz] at ha
        exact ⟨starLine (Γ.induce (subquadrangleSet Γ c P'))
            (subquadrangleColoring c P') x y,
          isStarLine_starLine hx hy hxyne, mem_starLine_left hx, mem_starLine_right hy, hzstar⟩
      obtain ⟨u, hu0, hxu, hyu, hzu⟩ :=
        exists_ptPerp_of_mem_clSet hΓ hF hx hy hz hxy4 hcl hzspan
      exact ⟨ptPerp (Γ.induce (subquadrangleSet Γ c P'))
          (subquadrangleColoring c P') {u},
        isStarPlane_ptPerp_singleton hP' hT' (subquadrangleColoring c P')
          (s := q ^ 2) (t := q) hdeg' hu0, hxu, hyu, hzu⟩
    · obtain ⟨u, v, hu0, huv4, hTP, hxu, hyu, hzu⟩ :=
        exists_traceSet_of_not_mem_clSet hΓ hF hx hy hz hxy4 hcl
      exact ⟨subquadrangleTrace Γ c P' u v,
        isStarPlane_subquadrangleTrace hΓ hF hu0 huv4 hTP hxu hyu hzu hnc,
        hxu, hyu, hzu⟩

end CFSG.Geometry.GeneralizedQuadrangles
