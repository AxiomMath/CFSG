module

public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Closure2
public import CFSG.Geometry.GeneralizedQuadrangles.Counting.Substructure
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem neighborSet_commonNeighbor_subset_spanUnion_of_trans
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M x1 x2 y1 y2 x y : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hx1L : Γ.Adj L x1) (hx2M : Γ.Adj M x2) (h2x : Γ.dist x1 x2 = 2)
    (hxV : x ∈ Γ.neighborSet (commonNeighbor hP h2x))
    (hy1L : Γ.Adj L y1) (hy2M : Γ.Adj M y2) (h2y : Γ.dist y1 y2 = 2)
    (hyV : y ∈ Γ.neighborSet (commonNeighbor hP h2y))
    (hxL : ¬ Γ.Adj L x) (hxM : ¬ Γ.Adj M x)
    (hyL : ¬ Γ.Adj L y) (hyM : ¬ Γ.Adj M y)
    (hxy : Γ.dist x y = 2) (h1 : 1 < p) (hx1y1 : x1 ≠ y1) :
    Γ.neighborSet (commonNeighbor hP hxy) ⊆ spanUnion hP L M := by
  classical
  have hLMne : L ≠ M := by
    intro hEq
    rw [hEq, SimpleGraph.dist_self] at hLM
    omega
  have hx10 : c x1 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hx1L
  have hx20 : c x2 = 0 := color_eq_zero_of_adj_of_color_eq_one hM hx2M
  have hy10 : c y1 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hy1L
  have hy20 : c y2 = 0 := color_eq_zero_of_adj_of_color_eq_one hM hy2M
  have hx2Lnot : ¬ Γ.Adj L x2 := by
    intro h
    have h1 : Γ.dist L x2 = 1 := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr h.symm
    have h2 : Γ.dist x2 M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hx2M.symm
    have htri := hP.connected.dist_triangle (u := L) (v := x2) (w := M)
    omega
  have hx2y2 : x2 ≠ y2 := by
    intro h
    subst h
    have h2yx : Γ.dist x2 x1 = 2 := by
      rw [SimpleGraph.dist_comm]
      exact h2x
    have h2yy : Γ.dist x2 y1 = 2 := by
      rw [SimpleGraph.dist_comm]
      exact h2y
    exact hx1y1 (eq_of_dist_two_of_mem_neighborSet hP c hL hx1L h2yx hy1L h2yy hx2Lnot)
  have hx2y1ne : x2 ≠ y1 := by
    intro h
    have hx2L : Γ.Adj L x2 := h ▸ hy1L
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := x2)
        hx2L hx2M.symm hLMne
    omega
  have h4 : Γ.dist x2 y1 = 4 := by
    rcases dist_eq_two_or_four_of_point_colors hP c hx20 hy10 hx2y1ne with h2 | h4
    · exfalso
      have hx2y2d : Γ.dist x2 y2 = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP (x := x2) (y := y2) (L := M)
          hx2M.symm hy2M hx2y2
      obtain ⟨W, hWall, huniq⟩ :=
        existsUnique_commonNeighbor_of_pairwise_dist_two hP h2 hx2y2d h2y
      have hWM : W = M :=
        (existsUnique_commonNeighbor hP hx2y2d).unique
          ⟨hWall.1, hWall.2.2⟩ ⟨hx2M.symm, hy2M.symm⟩
      have hy1M : Γ.Adj y1 M := hWM ▸ hWall.2.1
      have h2' : Γ.dist L M = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := y1)
          hy1L hy1M hLMne
      omega
    · exact h4
  have hpaircard : ({x2, y1} : Set V).ncard < (spanSet Γ x2 y1).ncard := by
    rw [Set.ncard_pair hx2y1ne, hp x2 y1 hx20 h4]
    omega
  obtain ⟨u, huS, huNot⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hpaircard (Set.toFinite _)
  have hux2 : u ≠ x2 := by
    intro h
    exact huNot (by rw [h]; simp)
  have huy1 : u ≠ y1 := by
    intro h
    exact huNot (by rw [h]; simp)
  have hx1y1d : Γ.dist x1 y1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP (x := x1) (y := y1) (L := L)
      hx1L.symm hy1L hx1y1
  have hx1trace : x1 ∈ traceSet Γ x2 y1 :=
    ⟨by rwa [SimpleGraph.dist_comm], by rw [SimpleGraph.dist_comm]; exact hx1y1d⟩
  have hx1u : Γ.dist x1 u = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT h4 huS hx1trace
  have hux1 : Γ.dist u x1 = 2 := by rw [SimpleGraph.dist_comm]; exact hx1u
  let N : V := commonNeighbor hP hx1u
  have hx1N : Γ.Adj x1 N := commonNeighbor_adj_left hP hx1u
  have huN : Γ.Adj u N := commonNeighbor_adj_right hP hx1u
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hx10 hx1N
  let W : V := commonNeighbor hP h2x
  have hx1W : Γ.Adj x1 W := commonNeighbor_adj_left hP h2x
  have hx2W : Γ.Adj x2 W := commonNeighbor_adj_right hP h2x
  have hW1 : c W = 1 := color_eq_one_of_adj_of_color_eq_zero hx10 hx1W
  have hLW : L ≠ W := by
    intro hEq
    exact hx2Lnot (hEq ▸ hx2W).symm
  obtain ⟨z1, hz1W, hz1ne⟩ := exists_adj_ne_of_isThick hT hx1W.symm
  obtain ⟨z2, hz2L, hz2ne⟩ := exists_adj_ne_of_isThick hT hx1L
  have hz10 : c z1 = 0 := color_eq_zero_of_adj_of_color_eq_one hW1 hz1W
  have hz20 : c z2 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hz2L
  have hz1z2 : Γ.dist z1 z2 = 4 :=
    dist_eq_four_of_mem_two_lines hP c hLW hL hW1 hx1L hx1W.symm hz1W hz1ne hz2L hz2ne
  have hx1z1 : Γ.dist x1 z1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hx1W hz1W (Ne.symm hz1ne)
  have hx1z2 : Γ.dist x1 z2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hx1L.symm hz2L (Ne.symm hz2ne)
  have hx2block : x2 ∈ spanBlock Γ x1 z1 z2 := by
    rw [spanBlock, mem_blockThrough]
    exact ⟨W, hx1W, ⟨z1, left_mem_spanSet hz1z2, hz1W⟩, hx2W.symm⟩
  have hy1block : y1 ∈ spanBlock Γ x1 z1 z2 := by
    rw [spanBlock, mem_blockThrough]
    exact ⟨L, hx1L.symm, ⟨z2, right_mem_spanSet hz1z2, hz2L⟩, hy1L⟩
  have hspanBlock : spanSet Γ x2 y1 ⊆ spanBlock Γ x1 z1 z2 :=
    spanSet_subset_spanBlock hP hT c (hH x1 hx10) hp hx10 hz10 hz20 hx1z1 hx1z2 hz1z2
      hx2block hy1block h4
  have hub : u ∈ spanBlock Γ x1 z1 z2 := hspanBlock huS
  have hNblock : Γ.neighborSet N ⊆ spanBlock Γ x1 z1 z2 := by
    rw [spanBlock, mem_blockThrough] at hub
    obtain ⟨T, hx1T, hTspan, hTu⟩ := hub
    have hTeq : T = N := eq_commonNeighbor hP hx1u hx1T hTu.symm
    intro v hv
    refine ⟨N, hx1N, ?_, hv⟩
    rw [← hTeq]
    exact hTspan
  have hNL : N ≠ L := by
    intro hEq
    have huL : Γ.Adj u L := hEq ▸ huN
    have hle : (spanSet Γ x2 y1 ∩ Γ.neighborSet L).ncard ≤ 1 :=
      ncard_spanSet_inter_neighborSet_le_one hP hT h4 L
    have hsub : ({u, y1} : Set V) ⊆ spanSet Γ x2 y1 ∩ Γ.neighborSet L := by
      intro v hv
      rcases hv with rfl | rfl
      · exact ⟨huS, huL.symm⟩
      · exact ⟨right_mem_spanSet h4, hy1L⟩
    have hpair : ({u, y1} : Set V).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hle
    rw [Set.ncard_pair huy1] at hpair
    omega
  have hNW : N ≠ W := by
    intro hEq
    have huW : Γ.Adj u W := hEq ▸ huN
    have huy2 : Γ.dist u x2 = 4 :=
      dist_eq_four_of_mem_span hP hT h4 huS (left_mem_spanSet h4) hux2
    have h2 : Γ.dist u x2 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := u) (y := x2) (L := W)
        huW hx2W.symm hux2
    omega
  have hNM : Γ.dist N M = 4 :=
    dist_eq_four_of_adj_line_of_ne hP c hM hL (by rwa [SimpleGraph.dist_comm])
      hx2M hx2W hx1W.symm hx1L hN1 hx1N.symm hNW
  have heq : spanUnion hP N M = spanUnion hP L M :=
    spanUnion_eq_of_block_symm hP hT c hH hdeg hp hL hM hLM hx2M hx2W hx1W.symm hx1L
      hz1W hz1ne hz2L hz2ne hz1z2 hN1 hNblock hNW hNL
  have hyP : y ∈ spanUnion hP L M := by
    apply spanOrLine_subset_spanUnion hP hy1L hy2M
    rw [spanOrLine_of_dist_eq_two hP h2y]
    exact hyV
  have hyN : y ∈ spanUnion hP N M := by
    rw [heq]
    exact hyP
  obtain ⟨v, w, hvN, hwM, hyvw⟩ := hyN
  have hv0 : c v = 0 := color_eq_zero_of_adj_of_color_eq_one hN1 hvN
  have hw0 : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hM hwM
  have hNMne : N ≠ M := by
    intro hEq
    rw [hEq, SimpleGraph.dist_self] at hNM
    omega
  have hvne : v ≠ w := by
    intro h
    have h2 : Γ.dist N M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := N) (y := M) (L := v)
        hvN (h ▸ hwM).symm hNMne
    omega
  have hvw4 : Γ.dist v w = 4 := by
    rcases dist_eq_two_or_four_of_point_colors hP c hv0 hw0 hvne with h2 | h4
    · exfalso
      let V2 : V := commonNeighbor hP h2y
      have hy1V2 : Γ.Adj y1 V2 := commonNeighbor_adj_left hP h2y
      have hy2V2 : Γ.Adj y2 V2 := commonNeighbor_adj_right hP h2y
      have hyne2 : y ≠ y2 := by
        intro h
        exact hyM (h ▸ hy2M)
      have hyy2 : Γ.dist y y2 = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := y2) (L := V2)
          hyV.symm hy2V2.symm hyne2
      let W2 : V := commonNeighbor hP h2
      have hvW : Γ.Adj v W2 := commonNeighbor_adj_left hP h2
      have hwW : Γ.Adj w W2 := commonNeighbor_adj_right hP h2
      have hyW : Γ.Adj W2 y := by
        rw [spanOrLine_of_dist_eq_two hP h2] at hyvw
        exact hyvw
      have hyw_ne : y ≠ w := by
        intro h
        exact hyM (h ▸ hwM)
      have hyw : Γ.dist y w = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := w) (L := W2)
          hyW.symm hwW.symm hyw_ne
      have hw_y2 : w = y2 :=
        (eq_of_dist_two_of_mem_neighborSet hP c hM hy2M hyy2 hwM hyw hyM).symm
      have hW2V2 : W2 = V2 :=
        (existsUnique_commonNeighbor hP hyy2).unique
          ⟨hyW.symm, hw_y2 ▸ hwW⟩ ⟨hyV.symm, hy2V2⟩
      have hvV2 : Γ.Adj V2 v := (hW2V2 ▸ hvW).symm
      have hNV2 : V2 ≠ N := by
        intro hEq
        have hV2x1 : Γ.Adj V2 x1 := (hEq ▸ hx1N).symm
        have hV2L : V2 = L :=
          eq_of_two_common_points hP hx1y1 hV2x1 hy1V2.symm hx1L hy1L
        have hLy2 : Γ.Adj L y2 := hV2L ▸ hy2V2.symm
        have h2' : Γ.dist L M = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := y2)
            hLy2 hy2M.symm hLMne
        omega
      have hres := eq_left_or_eq_right_of_three_lines hP
        (M := V2) (A := N) (B := L) (pA := v) (pB := y1) (u := x1)
        hNL hNV2 hvV2 hy1V2.symm hvN hx1N.symm hy1L hx1L
      rcases hres with hvx1 | hy1x1
      · have hvV2' : Γ.Adj V2 x1 := hvx1 ▸ hvV2
        have hV2L : V2 = L :=
          eq_of_two_common_points hP hx1y1 hvV2' hy1V2.symm hx1L hy1L
        have hLy2 : Γ.Adj L y2 := hV2L ▸ hy2V2.symm
        have h2' : Γ.dist L M = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := y2)
            hLy2 hy2M.symm hLMne
        omega
      · exact hx1y1 hy1x1.symm
    · exact h4
  have hyv : y ∈ spanSet Γ v w := by
    rw [spanOrLine_of_dist_eq_four hP hvw4] at hyvw
    exact hyvw
  have hyne_w : y ≠ w := by
    intro h
    exact hyM (h ▸ hwM)
  have hyne_v : y ≠ v := by
    intro h
    have hyblock : y ∈ spanBlock Γ x1 z1 z2 := by
      have hyNmem : y ∈ Γ.neighborSet N := by rw [h]; exact hvN
      exact hNblock hyNmem
    rw [spanBlock, mem_blockThrough] at hyblock
    obtain ⟨T, hx1T, hTspan, hTy⟩ := hyblock
    have hx1y : x1 ≠ y := by
      intro hxy'
      exact hyL (hxy' ▸ hx1L)
    have hyx1 : Γ.dist y x1 = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_adj_of_adj_of_ne hP (x := x1) (y := y) (L := T)
        hx1T hTy hx1y
    have hyy1 : Γ.dist y y1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := y) (y := y1)
        (L := commonNeighbor hP h2y) hyV.symm
        (commonNeighbor_adj_left hP h2y).symm (by
          intro hEq
          exact hyL (hEq ▸ hy1L))
    have : y1 = x1 :=
      eq_of_dist_two_of_mem_neighborSet hP c hL hy1L hyy1 hx1L hyx1 hyL
    exact hx1y1 this.symm
  have hxP : x ∈ spanUnion hP L M := by
    apply spanOrLine_subset_spanUnion hP hx1L hx2M
    rw [spanOrLine_of_dist_eq_two hP h2x]
    exact hxV
  have hxN : x ∈ spanUnion hP N M := by
    rw [heq]
    exact hxP
  have hres := neighborSet_commonNeighbor_subset_spanUnion_of_hyp hP hT c hH hdeg hp
    hN1 hM hNM hvN hwM hvw4 hyv hyne_v hyne_w hxN
    (by rw [SimpleGraph.dist_comm]; exact hxy)
  have hcomm : commonNeighbor hP (by rw [SimpleGraph.dist_comm]; exact hxy) =
      commonNeighbor hP hxy :=
    (existsUnique_commonNeighbor hP (by rw [SimpleGraph.dist_comm]; exact hxy)).unique
      ⟨commonNeighbor_adj_left hP (by rw [SimpleGraph.dist_comm]; exact hxy),
        commonNeighbor_adj_right hP (by rw [SimpleGraph.dist_comm]; exact hxy)⟩
      ⟨commonNeighbor_adj_right hP hxy, commonNeighbor_adj_left hP hxy⟩
  rw [hcomm] at hres
  rw [heq] at hres
  exact hres

theorem neighborSet_commonNeighbor_subset_spanUnion_of_mem_right
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M x y : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hxM : Γ.Adj M x) (hy : y ∈ spanUnion hP L M) (hxy : Γ.dist x y = 2) :
    Γ.neighborSet (commonNeighbor hP hxy) ⊆ spanUnion hP L M := by
  have h := neighborSet_commonNeighbor_subset_spanUnion_of_mem_left hP hT c hH hdeg hp
    hM hL (by rwa [SimpleGraph.dist_comm]) hxM (by rwa [← spanUnion_comm hP L M]) hxy
  rw [spanUnion_comm hP L M]
  exact h

private theorem isHyp_or_isTrans_of_mem_ne
    (hP : IsGeneralizedPolygon Γ 4) {L M a : V} (ha : a ∈ spanUnion hP L M)
    (haL : ¬ Γ.Adj L a) (haM : ¬ Γ.Adj M a) :
    (∃ x y : V, Γ.Adj L x ∧ Γ.Adj M y ∧ Γ.dist x y = 4 ∧
      a ∈ spanSet Γ x y ∧ a ≠ x ∧ a ≠ y) ∨
    (∃ (x y : V) (h2 : Γ.dist x y = 2),
      Γ.Adj L x ∧ Γ.Adj M y ∧ a ∈ Γ.neighborSet (commonNeighbor hP h2)) := by
  obtain ⟨x, y, hxL, hyM, haS⟩ := ha
  by_cases h4 : Γ.dist x y = 4
  · left
    refine ⟨x, y, hxL, hyM, h4, ?_, ?_, ?_⟩
    · rwa [spanOrLine_of_dist_eq_four hP h4] at haS
    · intro h
      exact haL (h ▸ hxL)
    · intro h
      exact haM (h ▸ hyM)
  · by_cases h2 : Γ.dist x y = 2
    · right
      refine ⟨x, y, h2, hxL, hyM, ?_⟩
      rwa [spanOrLine_of_dist_eq_two hP h2] at haS
    · have hnil : spanOrLine hP x y = ∅ := by
        rw [spanOrLine, if_neg h4, dif_neg h2]
      rw [hnil] at haS
      exact haS.elim


theorem lineClosure
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4) (h1 : 1 < p) :
    ∀ V : V, c V = 1 → 2 ≤ (Γ.neighborSet V ∩ spanUnion hP L M).ncard →
      Γ.neighborSet V ⊆ spanUnion hP L M := by
  classical
  have hLMne : L ≠ M := by
    intro hEq
    rw [hEq, SimpleGraph.dist_self] at hLM
    omega
  intro V hV hcard
  have hlt : 1 < (Γ.neighborSet V ∩ spanUnion hP L M).ncard := by omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard (s := Γ.neighborSet V ∩ spanUnion hP L M)).mp hlt
  obtain ⟨haN, haP⟩ := ha
  obtain ⟨hbN, hbP⟩ := hb
  have hdist : Γ.dist a b = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP haN.symm hbN hab
  have hVeq : V = commonNeighbor hP hdist :=
    eq_commonNeighbor hP hdist haN.symm hbN.symm
  have hcomm_ba : ∀ (h2 : Γ.dist b a = 2),
      commonNeighbor hP h2 = commonNeighbor hP hdist := by
    intro h2
    refine (existsUnique_commonNeighbor hP hdist).unique ?_ ?_
    · exact ⟨commonNeighbor_adj_right hP h2, commonNeighbor_adj_left hP h2⟩
    · exact ⟨commonNeighbor_adj_left hP hdist, commonNeighbor_adj_right hP hdist⟩
  rw [hVeq]
  by_cases haL : Γ.Adj L a
  · exact neighborSet_commonNeighbor_subset_spanUnion_of_mem_left hP hT c hH hdeg hp
      hL hM hLM haL hbP hdist
  by_cases haM : Γ.Adj M a
  · exact neighborSet_commonNeighbor_subset_spanUnion_of_mem_right hP hT c hH hdeg hp
      hL hM hLM haM hbP hdist
  rcases isHyp_or_isTrans_of_mem_ne hP haP haL haM with
    ⟨x, y, hxL, hyM, h4, haS, ha_ne_x, ha_ne_y⟩ |
    ⟨x, y, h2x, hxL, hyM, haV⟩
  · exact neighborSet_commonNeighbor_subset_spanUnion_of_hyp hP hT c hH hdeg hp
      hL hM hLM hxL hyM h4 haS ha_ne_x ha_ne_y hbP hdist
  by_cases hbL : Γ.Adj L b
  · have hres := neighborSet_commonNeighbor_subset_spanUnion_of_mem_left hP hT c hH hdeg hp
      hL hM hLM hbL haP (by rwa [SimpleGraph.dist_comm])
    rwa [hcomm_ba] at hres
  by_cases hbM : Γ.Adj M b
  · have hres := neighborSet_commonNeighbor_subset_spanUnion_of_mem_right hP hT c hH hdeg hp
      hL hM hLM hbM haP (by rwa [SimpleGraph.dist_comm])
    rwa [hcomm_ba] at hres
  rcases isHyp_or_isTrans_of_mem_ne hP hbP hbL hbM with
    ⟨x', y', hx'L, hy'M, h4', hbS, hb_ne_x', hb_ne_y'⟩ |
    ⟨x', y', h2y, hx'L, hy'M, hbV⟩
  · have hres := neighborSet_commonNeighbor_subset_spanUnion_of_hyp hP hT c hH hdeg hp
      hL hM hLM hx'L hy'M h4' hbS hb_ne_x' hb_ne_y' haP
      (by rwa [SimpleGraph.dist_comm])
    rwa [hcomm_ba] at hres
  · by_cases hxx' : x = x'
    ·
      subst x'
      have hxMnot : ¬ Γ.Adj M x := by
        intro hMx
        have h2 : Γ.dist L M = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := x)
            hxL hMx.symm hLMne
        omega
      have hy_eq : y = y' :=
        eq_of_dist_two_of_mem_neighborSet hP c hM hyM h2x hy'M h2y hxMnot
      subst y'
      have h2y' : commonNeighbor hP h2y = commonNeighbor hP h2x :=
        congrArg (commonNeighbor hP) (Subsingleton.elim h2y h2x)
      have hbV' : b ∈ Γ.neighborSet (commonNeighbor hP h2x) := by
        rwa [h2y'] at hbV
      have hcomm : commonNeighbor hP hdist = commonNeighbor hP h2x :=
        (eq_commonNeighbor hP hdist haV.symm hbV'.symm).symm
      rw [hcomm, ← spanOrLine_of_dist_eq_two hP h2x]
      exact spanOrLine_subset_spanUnion hP hxL hyM
    · exact neighborSet_commonNeighbor_subset_spanUnion_of_trans hP hT c hH hdeg hp
        hL hM hLM hxL hyM h2x haV hx'L hy'M h2y hbV haL haM hbL hbM hdist h1 hxx'

theorem exists_fullSubquadrangle
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {p : ℕ}
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    (h1 : 1 < p) (h2 : p < t) {L M : V} (hL : c L = 1) (hLM : Γ.dist L M = 4) :
    ∃ P' : Set V, Γ.neighborSet L ⊆ P' ∧ Γ.neighborSet M ⊆ P' ∧
      IsFullSubquadrangle c P' p := by
  have hM : c M = 1 := by
    have hc : c L = c M := (hP.eq_iff_even_dist c L M).2 (by rw [hLM]; exact ⟨2, by norm_num⟩)
    rw [hL] at hc
    exact hc.symm
  exact exists_fullSubquadrangle_of_lineClosure hP hT c hdeg hp hL hM hLM
    (lineClosure hP hT c hH hdeg hp hL hM hLM h1) h1 h2

private theorem exists_opposite_points
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hs : 0 < s) (ht : 0 < t) :
    ∃ x y : V, c x = 0 ∧ c y = 0 ∧ Γ.dist x y = 4 := by
  classical
  obtain ⟨L, hL⟩ := exists_line hP hT c
  have hposL : 0 < (Γ.neighborFinset L).card := by
    rw [card_neighborFinset_eq_degree]
    have := hT L
    omega
  obtain ⟨x, hxLf⟩ := Finset.card_pos.mp hposL
  have hxL : Γ.Adj L x := by simpa using hxLf
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
  have hpos : 0 < (Finset.univ.filter fun y => Γ.dist x y = 4).card := by
    rw [card_opposite hP hT c hdeg hx0]
    exact Nat.mul_pos (pow_pos hs 2) ht
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hy
  have hy0 : c y = 0 := by
    have hc : c x = c y :=
      (hP.eq_iff_even_dist c x y).2 (by rw [hy.2]; exact ⟨2, by norm_num⟩)
    rw [hx0] at hc
    exact hc.symm
  exact ⟨x, y, hx0, hy0, hy.2⟩

private theorem exists_opposite_lines
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) :
    ∃ L M : V, c L = 1 ∧ c M = 1 ∧ Γ.dist L M = 4 := by
  classical
  let dc : Γ.Coloring (Fin 2) := Γ.recolorOfEquiv (Equiv.swap (0 : Fin 2) 1) c
  have hdc0 : ∀ v, dc v = 0 ↔ c v = 1 := by
    intro v
    change Equiv.swap (0 : Fin 2) 1 (c v) = 0 ↔ c v = 1
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c v) with h | h <;> rw [h] <;> decide
  have hdeg' : ∀ v, Γ.degree v = if dc v = 0 then s + 1 else t + 1 := by
    intro v
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    by_cases hc0 : c v = 0
    · have hdc0' : dc v ≠ 0 := by
        intro h
        have h1 : c v = 1 := (hdc0 v).mp h
        rw [hc0] at h1
        exact absurd h1 (by decide)
      rw [hdeg v, if_pos hc0, if_neg hdc0']
    · have hc1 : c v = 1 := by
        rcases hfin (c v) with h | h
        · exact absurd h hc0
        · exact h
      have hdc0' : dc v = 0 := (hdc0 v).mpr hc1
      rw [hdeg v, if_neg hc0, if_pos hdc0']
  have hs : 0 < s := by
    have := two_le_s hP hT c hdeg
    omega
  have ht : 0 < t := by
    have := two_le_t hP hT c hdeg
    omega
  obtain ⟨L, M, hL0, hM0, hLM⟩ := exists_opposite_points hP hT dc hdeg' ht hs
  exact ⟨L, M, (hdc0 L).mp hL0, (hdc0 M).mp hM0, hLM⟩

private theorem trichotomy_arithmetic {s t p : ℕ} (hs : 0 < s) (hsle : s ≤ p ^ 2)
    (hsp : p * s ≤ t) (hpt : p * t ≤ s ^ 2) : s = p ^ 2 ∧ t = p ^ 3 := by
  have hp2s : p ^ 2 ≤ s := by
    have h1 : p ^ 2 * s ≤ s * s := by
      calc
        p ^ 2 * s = p * (p * s) := by ring
        _ ≤ p * t := Nat.mul_le_mul_left p hsp
        _ ≤ s ^ 2 := hpt
        _ = s * s := by ring
    exact Nat.le_of_mul_le_mul_right h1 hs
  have hseq : s = p ^ 2 := le_antisymm hsle hp2s
  have hp3t : p ^ 3 ≤ t := by
    calc
      p ^ 3 = p * p ^ 2 := by ring
      _ = p * s := by rw [hseq]
      _ ≤ t := hsp
  have ht3 : t ≤ p ^ 3 := by
    have hppos : 0 < p := by
      rcases Nat.eq_zero_or_pos p with h | h
      · rw [h] at hsle
        simp at hsle
        omega
      · exact h
    have h : p * t ≤ p * p ^ 3 := by
      calc
        p * t ≤ s ^ 2 := hpt
        _ = p ^ 4 := by rw [hseq]; ring
        _ = p * p ^ 3 := by ring
    exact Nat.le_of_mul_le_mul_left h hppos
  exact ⟨hseq, le_antisymm ht3 hp3t⟩

theorem isFullSubquadrangle_spanUnion
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t p : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLC : ∀ V : V, c V = 1 →
      2 ≤ (Γ.neighborSet V ∩ spanUnion hP L M).ncard →
      Γ.neighborSet V ⊆ spanUnion hP L M)
    (h1 : 1 < p) (h2 : p < t) :
    IsFullSubquadrangle c (spanUnion hP L M) p := by
  classical
  let P : Set V := spanUnion hP L M
  let h0 : ∀ x ∈ P, c x = 0 :=
    fun x hx => color_zero_of_mem_spanUnion hP hT c hL hM hLM hx
  have hfull : ∀ L' : V, c L' = 1 → 2 ≤ (Γ.neighborSet L' ∩ P).ncard →
      Γ.neighborSet L' ⊆ P := hLC
  have hquad : ∃ x ∈ P, ∃ y ∈ P, Γ.dist x y = 4 ∧
      2 ≤ (traceSet Γ x y ∩ P).ncard :=
    exists_quadrangle_spanUnion hP hT c hdeg hL hM hLM
  obtain ⟨t', -, hF, hcount, -⟩ :=
    exists_fullSubquadrangle_structure hP hT c hdeg h0 hfull hquad
  have hcountP : P.ncard = (s + 1) * (s * p + 1) :=
    ncard_spanUnion hP hT c hdeg hp hL hM hLM
  have ht'p : t' = p := by
    have hmul : (s + 1) * (s * t' + 1) = (s + 1) * (s * p + 1) := by
      rw [← hcount, hcountP]
    have hsucc : s * t' + 1 = s * p + 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.succ_pos s) hmul
    have hst : s * t' = s * p := by omega
    have hs : 0 < s := by
      have := two_le_s hP hT c hdeg
      omega
    exact Nat.mul_left_cancel hs hst
  simpa [P, ht'p] using hF

theorem trichotomy
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {p : ℕ}
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1) :
    p = t ∨ p = 1 ∨ (s = p ^ 2 ∧ t = p ^ 3) := by
  classical
  have hs : 0 < s := by
    have := two_le_s hP hT c hdeg
    omega
  have ht : 0 < t := by
    have := two_le_t hP hT c hdeg
    omega
  have hp_le_t : p ≤ t := by
    obtain ⟨x, y, hx0, hy0, hxy4⟩ := exists_opposite_points hP hT c hdeg hs ht
    let X : Finset V := (spanSet Γ x y).toFinset
    have hXsub : (X : Set V) ⊆ spanSet Γ x y := by
      intro z hz
      simpa [X] using hz
    have hXcard : X.card = p + 1 := by
      rw [show X.card = (spanSet Γ x y).ncard by rw [Set.ncard_eq_toFinset_card']]
      exact hp x y hx0 hxy4
    have hle := card_le_t_add_one_of_subset_span hP hT c hdeg hx0 hxy4 hXsub
    omega
  by_cases hpt : p = t
  · exact Or.inl hpt
  by_cases hp1 : p = 1
  · exact Or.inr (Or.inl hp1)
  right
  right
  have hp_pos : 1 ≤ p := by
    obtain ⟨x, y, hx0, hy0, hxy4⟩ := exists_opposite_points hP hT c hdeg hs ht
    have hcard : (spanSet Γ x y).ncard = p + 1 := hp x y hx0 hxy4
    have h2 : 2 ≤ (spanSet Γ x y).ncard := by
      have hne : x ≠ y := by
        intro h
        rw [h, SimpleGraph.dist_self] at hxy4
        omega
      have hlt : 1 < (spanSet Γ x y).ncard :=
        (Set.one_lt_ncard (s := spanSet Γ x y)).mpr
          ⟨x, left_mem_spanSet hxy4, y, right_mem_spanSet hxy4, hne⟩
      omega
    omega
  have h1 : 1 < p := by omega
  have h2 : p < t := by omega
  obtain ⟨L, M, hL, hM, hLM⟩ := exists_opposite_lines hP hT c hdeg
  let P' : Set V := spanUnion hP L M
  have hLC : ∀ V : V, c V = 1 → 2 ≤ (Γ.neighborSet V ∩ P').ncard →
      Γ.neighborSet V ⊆ P' :=
    lineClosure hP hT c hH hdeg hp hL hM hLM h1
  have hF : IsFullSubquadrangle c P' p :=
    isFullSubquadrangle_spanUnion hP hT c hdeg hp hL hM hLM hLC h1 h2
  let S : Set V := subquadrangleSet Γ c P'
  let G : SimpleGraph S := Γ.induce S
  let c' : G.Coloring (Fin 2) := SimpleGraph.Coloring.mk (fun v : S => c v.1) (by
    intro u v huv
    exact c.valid (SimpleGraph.induce_adj.mp huv))
  have hGQ : IsGeneralizedPolygon G 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hdeg hF
  have hThick : IsThick G :=
    isThick_subquadrangleGraph hP hT c hdeg hF (by omega)
  have hdeg' : ∀ v : S, G.degree v = if c' v = 0 then p + 1 else s + 1 := by
    intro v
    by_cases hv : c' v = 0
    · rw [if_pos hv]
      have hvP : v.1 ∈ P' := by
        rcases mem_subquadrangleSet.mp v.2 with h | h
        · exact h
        · have hv0 : c v.1 = 0 := hv
          exact absurd (h.1.symm.trans hv0) (by decide)
      simpa using degree_subquadrangleGraph_of_mem_point c hF hvP
    · rw [if_neg hv]
      have hv1 : c v.1 = 1 := by
        have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
        rcases hfin (c v.1) with h | h
        · exact absurd h hv
        · exact h
      have hline : v.1 ∈ subquadrangleLines Γ c P' := by
        rcases mem_subquadrangleSet.mp v.2 with h | h
        · exact absurd (hF.1 v.1 h) (by rw [hv1]; decide)
        · exact h
      simpa using degree_subquadrangleGraph_of_mem_line c hdeg hF hline
  have hsle : s ≤ p ^ 2 := higman_s_le_t_sq hGQ hThick c' hdeg'
  let B : Set V := {L' | c L' = 1 ∧ Γ.neighborSet L' ⊆ P'}
  have hFB : ∀ x ∈ P', (Γ.neighborSet x ∩ B).ncard = p + 1 := by
    intro x hx
    have hEq : Γ.neighborSet x ∩ B = fullLinesThrough Γ P' x := by
      ext L'
      constructor
      · rintro ⟨hxL, hc, hsub⟩
        exact ⟨hxL, hsub⟩
      · rintro ⟨hxL, hsub⟩
        exact ⟨hxL, ⟨color_eq_one_of_adj_of_color_eq_zero (hF.1 x hx) hxL, hsub⟩⟩
    rw [hEq]
    exact hF.2.2.1 x hx
  have hFF : ∀ x ∈ P', ∀ y ∈ P', x ≠ y → ∀ L' : V, Γ.Adj x L' → Γ.Adj y L' →
      L' ∈ B := by
    intro x hx y hy hxy L' hxL hyL
    have hc : c L' = 1 := color_eq_one_of_adj_of_color_eq_zero (hF.1 x hx) hxL
    have hdist2 : Γ.dist x y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hxL hyL.symm hxy
    have hcard : 2 ≤ (Γ.neighborSet L' ∩ P').ncard := by
      have hlt : 1 < (Γ.neighborSet L' ∩ P').ncard :=
        (Set.one_lt_ncard (s := Γ.neighborSet L' ∩ P')).mpr
          ⟨x, ⟨hxL.symm, hx⟩, y, ⟨hyL.symm, hy⟩, hxy⟩
      omega
    exact ⟨hc, hLC L' hc hcard⟩
  obtain ⟨x0, hx0P, -, -⟩ := hF.2.2.2
  have hsp : p * s ≤ t := by
    rcases eq_or_mul_le_of_closed_dual hP hT c hdeg (F := P') (B := B) (p := p)
      hF.1 (fun L' h => h.1) (fun L' h x hx => h.2 hx) hFB hFF ⟨x0, hx0P⟩ with hpt' | hps
    · exact absurd hpt' hpt
    · exact hps
  have hpt_le : p * t ≤ s ^ 2 := by
    obtain ⟨x, y, hx0, hy0, hxy4⟩ := exists_opposite_points hP hT c hdeg hs ht
    let X : Finset V := (spanSet Γ x y).toFinset
    have hXsub : (X : Set V) ⊆ spanSet Γ x y := by
      intro z hz
      simpa [X] using hz
    have hXcard : X.card = p + 1 := by
      rw [show X.card = (spanSet Γ x y).ncard by rw [Set.ncard_eq_toFinset_card']]
      exact hp x y hx0 hxy4
    have hm : 2 ≤ X.card := by rw [hXcard]; omega
    have hres := mul_le_sq_of_subset_span hP hT c hdeg hx0 hxy4 hXsub hm
    rw [hXcard] at hres
    simpa using hres
  exact trichotomy_arithmetic hs hsle hsp hpt_le

end CFSG.Geometry.GeneralizedQuadrangles
