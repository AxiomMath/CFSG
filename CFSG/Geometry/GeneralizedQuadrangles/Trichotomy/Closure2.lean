module

public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Closure
public import CFSG.Geometry.GeneralizedQuadrangles.Subquadrangle2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem exists_quadrangle_spanUnion
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {L M : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4) :
    ∃ x ∈ spanUnion hP L M, ∃ y ∈ spanUnion hP L M,
      Γ.dist x y = 4 ∧ 2 ≤ (traceSet Γ x y ∩ spanUnion hP L M).ncard := by
  classical
  have hLMne : L ≠ M := by
    intro hEq
    rw [hEq, SimpleGraph.dist_self] at hLM
    omega
  have hposL : 0 < (Γ.neighborFinset L).card := by
    rw [card_neighborFinset_eq_degree]
    have := hT L
    omega
  obtain ⟨x, hxLf⟩ := Finset.card_pos.mp hposL
  have hxL : Γ.Adj L x := by simpa using hxLf
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
  obtain ⟨yx, hyxspec, huniq⟩ :=
    existsUnique_adj_dist_two_of_mem_neighborSet hP c hL hxL hM hLM
  obtain ⟨hyxM, hyxd⟩ := hyxspec
  have hyxMf : yx ∈ Γ.neighborFinset M := by simpa using hyxM
  have hposErase : 0 < ((Γ.neighborFinset M).erase yx).card := by
    rw [Finset.card_erase_of_mem hyxMf]
    rw [card_neighborFinset_eq_degree]
    have := hT M
    omega
  obtain ⟨y, hyerase⟩ := Finset.card_pos.mp hposErase
  rw [Finset.mem_erase, mem_neighborFinset] at hyerase
  obtain ⟨hyne, hyM⟩ := hyerase
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hyM
  have hxyne : x ≠ y := by
    intro hEq
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hxL (hEq ▸ hyM).symm hLMne
    omega
  have hxy4' : Γ.dist x y = 4 := by
    rcases dist_eq_two_or_four_of_point_colors hP c hx0 hy0 hxyne with h2 | h4
    · exfalso
      exact hyne (huniq y ⟨hyM, h2⟩)
    · exact h4
  have hyLnot : ¬ Γ.Adj y L := by
    intro h
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP (x := L) (y := M) (L := y) h.symm hyM.symm hLMne
    omega
  have hyL3 : Γ.dist y L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hyLnot (by rw [hy0, hL]; decide)
  let xy : V := proj hP hyL3
  have hxyL : Γ.Adj L xy := proj_adj hP hyL3
  have hxyd : Γ.dist y xy = 2 := proj_dist hP hyL3
  have hxy_ne_x : xy ≠ x := by
    intro hEq
    rw [hEq, SimpleGraph.dist_comm] at hxyd
    omega
  have htrace_xy : xy ∈ traceSet Γ x y := by
    refine ⟨?_, hxyd⟩
    exact dist_eq_two_of_adj_of_adj_of_ne hP hxL.symm hxyL (Ne.symm hxy_ne_x)
  have htrace_yx : yx ∈ traceSet Γ x y := by
    refine ⟨hyxd, ?_⟩
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_adj_of_adj_of_ne hP (x := yx) (y := y) (L := M) hyxM.symm hyM hyne.symm
  have hxP : x ∈ spanUnion hP L M :=
    neighborSet_subset_spanUnion_left hP hT c hL hM hLM hxL
  have hyP : y ∈ spanUnion hP L M :=
    neighborSet_subset_spanUnion_right hP hT c hL hM hLM hyM
  have hxyP : xy ∈ spanUnion hP L M :=
    neighborSet_subset_spanUnion_left hP hT c hL hM hLM hxyL
  have hyxP : yx ∈ spanUnion hP L M :=
    neighborSet_subset_spanUnion_right hP hT c hL hM hLM hyxM
  have hne : xy ≠ yx := by
    intro hEq
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hxyL (hEq ▸ hyxM).symm hLMne
    omega
  refine ⟨x, hxP, y, hyP, hxy4', ?_⟩
  have hlt : 1 < (traceSet Γ x y ∩ spanUnion hP L M).ncard :=
    (Set.one_lt_ncard (s := traceSet Γ x y ∩ spanUnion hP L M)).mpr
      ⟨xy, ⟨htrace_xy, hxyP⟩, yx, ⟨htrace_yx, hyxP⟩, hne⟩
  omega


theorem exists_fullSubquadrangle_of_lineClosure
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t p : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLC : ∀ V : V, c V = 1 → 2 ≤ (Γ.neighborSet V ∩ spanUnion hP L M).ncard →
      Γ.neighborSet V ⊆ spanUnion hP L M) (h1 : 1 < p) (h2 : p < t) :
    ∃ P' : Set V, Γ.neighborSet L ⊆ P' ∧ Γ.neighborSet M ⊆ P' ∧
      IsFullSubquadrangle c P' p := by
  classical
  let P : Set V := spanUnion hP L M
  have h0 : ∀ x ∈ P, c x = 0 := fun x hx => color_zero_of_mem_spanUnion hP hT c hL hM hLM hx
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
  refine ⟨P, neighborSet_subset_spanUnion_left hP hT c hL hM hLM,
    neighborSet_subset_spanUnion_right hP hT c hL hM hLM, ?_⟩
  simpa [P, ht'p] using hF


theorem neighborSet_commonNeighbor_subset_spanUnion_of_hyp
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M x1 x2 x y : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hx1L : Γ.Adj L x1) (hx2M : Γ.Adj M x2) (h4 : Γ.dist x1 x2 = 4)
    (hx : x ∈ spanSet Γ x1 x2) (hxne1 : x ≠ x1) (hxne2 : x ≠ x2)
    (hy : y ∈ spanUnion hP L M) (hxy : Γ.dist x y = 2) :
    Γ.neighborSet (commonNeighbor hP hxy) ⊆ spanUnion hP L M := by
  classical
  have hx0 : c x = 0 := by
    rw [color_eq_of_mem_span hP hT c h4 hx]
    exact color_eq_zero_of_adj_of_color_eq_one hL hx1L
  have hxNotL : ¬ Γ.Adj L x := by
    intro hxL
    have hle : (spanSet Γ x1 x2 ∩ Γ.neighborSet L).ncard ≤ 1 :=
      ncard_spanSet_inter_neighborSet_le_one hP hT h4 L
    have hsub : ({x, x1} : Set V) ⊆ spanSet Γ x1 x2 ∩ Γ.neighborSet L := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨hx, hxL⟩
      · exact ⟨left_mem_spanSet h4, hx1L⟩
    have hpair : ({x, x1} : Set V).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hle
    have : x = x1 := by
      by_contra hne
      rw [Set.ncard_pair hne] at hpair
      omega
    exact hxne1 this
  have hnotAdj : ¬ Γ.Adj x2 L := by
    intro h
    have h1 : Γ.dist L x2 = 1 := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr h
    have h2 : Γ.dist x2 M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hx2M.symm
    have htri := hP.connected.dist_triangle (u := L) (v := x2) (w := M)
    omega
  have hx20 : c x2 = 0 := color_eq_zero_of_adj_of_color_eq_one hM hx2M
  have hx2L3 : Γ.dist x2 L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hnotAdj (by rw [hx20, hL]; decide)
  let z : V := proj hP hx2L3
  have hzL : Γ.Adj L z := proj_adj hP hx2L3
  have hzx2 : Γ.dist z x2 = 2 := by
    rw [SimpleGraph.dist_comm]
    exact proj_dist hP hx2L3
  have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hzL
  have hz_ne_x1 : z ≠ x1 := by
    intro h
    rw [h] at hzx2
    omega
  have hzx1 : Γ.dist z x1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hzL.symm hx1L hz_ne_x1
  have hztrace : z ∈ traceSet Γ x1 x2 :=
    ⟨by rwa [SimpleGraph.dist_comm], by rwa [SimpleGraph.dist_comm]⟩
  have hzx : Γ.dist z x = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hT h4 hx hztrace
  have hxz : Γ.dist x z = 2 := by rw [SimpleGraph.dist_comm]; exact hzx
  let W : V := commonNeighbor hP hzx2
  have hzW : Γ.Adj z W := commonNeighbor_adj_left hP hzx2
  have hx2W : Γ.Adj x2 W := commonNeighbor_adj_right hP hzx2
  have hW1 : c W = 1 := color_eq_one_of_adj_of_color_eq_zero hz0 hzW
  have hLW : L ≠ W := by
    intro hEq
    exact hnotAdj (hEq ▸ hx2W)
  obtain ⟨z1, hz1W, hz1ne⟩ := exists_adj_ne_of_isThick hT hzW.symm
  obtain ⟨z2, hz2L, hz2ne⟩ := exists_adj_ne_of_isThick hT hzL
  have hz10 : c z1 = 0 := color_eq_zero_of_adj_of_color_eq_one hW1 hz1W
  have hz20 : c z2 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hz2L
  have hz1z2 : Γ.dist z1 z2 = 4 :=
    dist_eq_four_of_mem_two_lines hP c hLW hL hW1 hzL hzW.symm hz1W hz1ne hz2L hz2ne
  have hzz1 : Γ.dist z z1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hzW hz1W (Ne.symm hz1ne)
  have hzz2 : Γ.dist z z2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hzL.symm hz2L (Ne.symm hz2ne)
  have hx1block : x1 ∈ spanBlock Γ z z1 z2 := by
    rw [spanBlock, mem_blockThrough]
    exact ⟨L, hzL.symm, ⟨z2, right_mem_spanSet hz1z2, hz2L⟩, hx1L⟩
  have hx2block : x2 ∈ spanBlock Γ z z1 z2 := by
    rw [spanBlock, mem_blockThrough]
    exact ⟨W, hzW, ⟨z1, left_mem_spanSet hz1z2, hz1W⟩, hx2W.symm⟩
  have hspanBlock : spanSet Γ x1 x2 ⊆ spanBlock Γ z z1 z2 :=
    spanSet_subset_spanBlock hP hT c (hH z hz0) hp hz0 hz10 hz20 hzz1 hzz2 hz1z2
      hx1block hx2block h4
  have hxblock : x ∈ spanBlock Γ z z1 z2 := hspanBlock hx
  have hNblock : Γ.neighborSet (commonNeighbor hP hxz) ⊆ spanBlock Γ z z1 z2 := by
    rw [spanBlock, mem_blockThrough] at hxblock
    obtain ⟨T, hzT, hTspan, hTx⟩ := hxblock
    have hTeq : T = commonNeighbor hP hxz := eq_commonNeighbor hP hxz hTx.symm hzT
    intro u hu
    refine ⟨commonNeighbor hP hxz, commonNeighbor_adj_right hP hxz, ?_, hu⟩
    rw [← hTeq]
    exact hTspan
  have hN1 : c (commonNeighbor hP hxz) = 1 :=
    color_eq_one_of_adj_of_color_eq_zero hx0 (commonNeighbor_adj_left hP hxz)
  have hNL : commonNeighbor hP hxz ≠ L := by
    intro hEq
    have : Γ.Adj x L := hEq ▸ commonNeighbor_adj_left hP hxz
    exact hxNotL this.symm
  have hNW : commonNeighbor hP hxz ≠ W := by
    intro hEq
    have hxW : Γ.Adj x W := hEq ▸ commonNeighbor_adj_left hP hxz
    have hx2W' : Γ.Adj x2 W := hx2W
    have hxW' : x ∈ spanSet Γ x1 x2 ∩ Γ.neighborSet W := ⟨hx, hxW.symm⟩
    have hle : (spanSet Γ x1 x2 ∩ Γ.neighborSet W).ncard ≤ 1 :=
      ncard_spanSet_inter_neighborSet_le_one hP hT h4 W
    have hsub : ({x, x2} : Set V) ⊆ spanSet Γ x1 x2 ∩ Γ.neighborSet W := by
      intro u hu
      rcases hu with rfl | rfl
      · exact ⟨hx, hxW.symm⟩
      · exact ⟨right_mem_spanSet h4, hx2W'.symm⟩
    have hpair : ({x, x2} : Set V).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hle
    have hxneq : x ≠ x2 := hxne2
    rw [Set.ncard_pair hxneq] at hpair
    omega
  have hNM : Γ.dist (commonNeighbor hP hxz) M = 4 :=
    dist_eq_four_of_adj_line_of_ne hP c hM hL (by rwa [SimpleGraph.dist_comm])
      hx2M hx2W hzW.symm hzL hN1 (commonNeighbor_adj_right hP hxz).symm hNW
  have heq : spanUnion hP (commonNeighbor hP hxz) M = spanUnion hP L M :=
    spanUnion_eq_of_block_symm hP hT c hH hdeg hp hL hM hLM hx2M hx2W hzW.symm hzL
      hz1W hz1ne hz2L hz2ne hz1z2 hN1 hNblock hNW hNL
  have hy' : y ∈ spanUnion hP (commonNeighbor hP hxz) M := by rw [heq]; exact hy
  have hres := neighborSet_commonNeighbor_subset_spanUnion_of_mem_left hP hT c hH hdeg hp
    hN1 hM hNM (commonNeighbor_adj_left hP hxz).symm hy' hxy
  rwa [heq] at hres

end CFSG.Geometry.GeneralizedQuadrangles
