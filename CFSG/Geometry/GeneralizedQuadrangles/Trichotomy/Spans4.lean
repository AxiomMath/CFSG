module

public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Spans3
public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Spans2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section LineThrough

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem adj_of_neighborSet_subset_spanBlock
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {y N z1 z2 : V} (hy : c y = 0) (hN : c N = 1)
    (hsub : Γ.neighborSet N ⊆ spanBlock Γ y z1 z2) : Γ.Adj N y := by
  classical
  by_contra hNy
  have hyN3 : Γ.dist y N = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hNy h.symm) (by rw [hy, hN]; decide)
  obtain ⟨w, -, huniq⟩ := existsUnique_proj hP hyN3
  have hncard : (Γ.neighborSet N).ncard = Γ.degree N :=
    SimpleGraph.ncard_neighborSet Γ N
  have hlt : 1 < (Γ.neighborSet N).ncard := by
    rw [hncard]
    exact lt_of_lt_of_le (by norm_num) (hT N)
  obtain ⟨u, hu, v, hv, huv⟩ := (Set.one_lt_ncard (s := Γ.neighborSet N)).mp hlt
  have hu_span : u ∈ spanBlock Γ y z1 z2 := hsub hu
  have hv_span : v ∈ spanBlock Γ y z1 z2 := hsub hv
  have huB : u ∈ blockThrough Γ y (spanSet Γ z1 z2) := hu_span
  have hvB : v ∈ blockThrough Γ y (spanSet Γ z1 z2) := hv_span
  rw [mem_blockThrough] at huB hvB
  obtain ⟨Tu, hyTu, -, hTuu⟩ := huB
  obtain ⟨Tv, hyTv, -, hTvv⟩ := hvB
  have huy : u ≠ y := fun h => hNy (h ▸ hu)
  have hvy : v ≠ y := fun h => hNy (h ▸ hv)
  have hyu : Γ.dist y u = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyTu hTuu huy.symm
  have hyv : Γ.dist y v = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hyTv hTvv hvy.symm
  exact huv ((huniq u ⟨hu, hyu⟩).trans (huniq v ⟨hv, hyv⟩).symm)

end LineThrough

section Opposite

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem dist_eq_four_of_adj_line_of_ne
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L M N W x y : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hxW : Γ.Adj x W) (hWy : Γ.Adj W y) (hMy : Γ.Adj M y)
    (hN : c N = 1) (hNy : Γ.Adj N y) (hNW : N ≠ W) : Γ.dist N L = 4 := by
  classical
  have hLMne : L ≠ M := by
    intro hEq
    rw [hEq, SimpleGraph.dist_self] at hLM
    omega
  have hyL : ¬ Γ.Adj L y := by
    intro hLy
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLy hMy.symm hLMne
    omega
  have hxy_ne : x ≠ y := fun h => hyL (h.symm ▸ hLx)
  have hyx : Γ.dist y x = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hWy.symm hxW.symm hxy_ne.symm
  have hNL_ne : N ≠ L := by
    intro hEq
    exact hyL (hEq ▸ hNy)
  have hnot2 : Γ.dist N L ≠ 2 := by
    intro h2
    obtain ⟨p, hp, -⟩ := existsUnique_commonNeighbor hP h2
    have hpy : p ≠ y := by
      intro hEq
      exact hyL (hEq ▸ hp.2)
    have hyp : Γ.dist y p = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hNy.symm hp.1 hpy.symm
    have hyL3 : Γ.dist y L = 3 := by
      have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMy
      exact dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hyL h.symm)
        (by rw [hy0, hL]; decide)
    have hpx : p = x :=
      (existsUnique_proj hP hyL3).unique ⟨hp.2, hyp⟩ ⟨hLx, hyx⟩
    have hNx : Γ.Adj N x := hpx ▸ hp.1
    have hNW_eq : N = W :=
      (existsUnique_commonNeighbor hP hyx).unique
        ⟨hNy.symm, hNx.symm⟩ ⟨hWy.symm, hxW⟩
    exact hNW hNW_eq
  have heven : Even (Γ.dist N L) :=
    (hP.eq_iff_even_dist c N L).1 (by rw [hN, hL])
  have hle : Γ.dist N L ≤ 4 := hP.dist_le (by norm_num) N L
  have hne0 : Γ.dist N L ≠ 0 := by
    intro h0
    exact hNL_ne ((hP.connected.dist_eq_zero_iff).mp h0)
  obtain ⟨k, hk⟩ := heven
  omega

end Opposite

section MeetsSpan

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem exists_spanSet_adj_of_mem_spanBlock_of_ne
    (hP : IsGeneralizedPolygon Γ 4) {y N a z1 z2 : V}
    (hNy : Γ.Adj N y) (hNa : Γ.Adj N a) (hay : a ≠ y)
    (haB : a ∈ spanBlock Γ y z1 z2) :
    ∃ t ∈ spanSet Γ z1 z2, Γ.Adj N t := by
  rw [spanBlock, mem_blockThrough] at haB
  obtain ⟨T, hyT, ⟨t, ht, hTt⟩, hTa⟩ := haB
  have hya : Γ.dist y a = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hNy.symm hNa hay.symm
  have hTN : T = N := by
    rw [eq_commonNeighbor hP hya hyT hTa.symm, eq_commonNeighbor hP hya hNy.symm hNa.symm]
  exact ⟨t, ht, hTN ▸ hTt⟩

end MeetsSpan

section Projection

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem mem_spanSet_of_mem_spanBlock_of_ne
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {L M N W x y z1 z2 a b yb : V}
    (hL : c L = 1) (hM : c M = 1) (hN : c N = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hxW : Γ.Adj x W) (hWy : Γ.Adj W y) (hMy : Γ.Adj M y)
    (hz1W : Γ.Adj W z1) (hz1y : z1 ≠ y) (hz2M : Γ.Adj M z2) (hz2y : z2 ≠ y)
    (hz1z2 : Γ.dist z1 z2 = 4)
    (hNy : Γ.Adj N y) (hNM : N ≠ M)
    (hNsub : Γ.neighborSet N ⊆ spanBlock Γ y z1 z2)
    (hNa : Γ.Adj N a) (hay : a ≠ y)
    (hLb : Γ.Adj L b) (hbx : b ≠ x) (hba : Γ.dist b a = 2)
    (hMyb : Γ.Adj M yb) (hbyb : Γ.dist b yb = 2) (hayb : Γ.dist a yb = 4) :
    x ∈ spanSet Γ a yb := by
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMy
  have hNT : ∃ t ∈ spanSet Γ z1 z2, Γ.Adj N t :=
    exists_spanSet_adj_of_mem_spanBlock_of_ne hP hNy hNa hay (hNsub hNa)
  exact mem_spanSet_of_mem_block_projection hP hT c (hH y hy0) hp
    hL hM hN hLM hLx hLb hbx hxW hWy hz1W hz1y hMy hMyb hbyb
    hNy hNM hNT hNa hba hay hayb hz2M hz2y hz1z2

end Projection

section Main

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem spanOrLine_subset_spanUnion_of_ne
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {s t : ℕ} (hdeg : ∀ v : V, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {L M x W y z1 z2 N a b : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hxW : Γ.Adj x W) (hWy : Γ.Adj W y) (hMy : Γ.Adj M y)
    (hz1W : Γ.Adj W z1) (hz1y : z1 ≠ y) (hz2M : Γ.Adj M z2) (hz2y : z2 ≠ y)
    (hz1z2 : Γ.dist z1 z2 = 4)
    (hN : c N = 1) (hNy : Γ.Adj N y) (hNW : N ≠ W) (hNM : N ≠ M)
    (hNsub : Γ.neighborSet N ⊆ spanBlock Γ y z1 z2)
    (hNa : Γ.Adj N a) (hLb : Γ.Adj L b) (hay : a ≠ y) :
    spanOrLine hP a b ⊆ spanUnion hP L M := by
  classical
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMy
  have hya : Γ.dist y a = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hNy.symm hNa hay.symm
  have hLMne : L ≠ M := by
    intro hEq
    rw [hEq, SimpleGraph.dist_self] at hLM
    omega
  have hyL : ¬ Γ.Adj L y := by
    intro hLy
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLy hMy.symm hLMne
    omega
  have hyL3 : Γ.dist y L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hyL h.symm)
      (by rw [hy0, hL]; decide)
  have hxy_ne : x ≠ y := fun h => hyL (h.symm ▸ hLx)
  have hyx : Γ.dist y x = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hWy.symm hxW.symm hxy_ne.symm
  have haL : ¬ Γ.Adj L a := by
    intro hLa
    have hax : a = x :=
      (existsUnique_proj hP hyL3).unique ⟨hLa, hya⟩ ⟨hLx, hyx⟩
    have hNx : Γ.Adj N x := hax ▸ hNa
    have hNW_eq : N = W :=
      (existsUnique_commonNeighbor hP hyx).unique
        ⟨hNy.symm, hNx.symm⟩ ⟨hWy.symm, hxW⟩
    exact hNW hNW_eq
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hN hNa
  have h3a : Γ.dist a L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => haL h.symm)
      (by rw [ha0, hL]; decide)
  let ba : V := proj hP h3a
  have hLba : Γ.Adj L ba := proj_adj hP h3a
  have hba : Γ.dist ba a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact proj_dist hP h3a
  have hba0 : c ba = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLba
  have hbx : ba ≠ x := by
    intro hbax
    have hxa : Γ.dist x a = 2 := hbax ▸ hba
    have hxy : Γ.dist x y = 2 := by
      rw [SimpleGraph.dist_comm]
      exact hyx
    obtain ⟨T, hT, -⟩ :=
      existsUnique_commonNeighbor_of_pairwise_dist_two hP hxy hxa hya
    have hTW : T = W :=
      (existsUnique_commonNeighbor hP hxy).unique ⟨hT.1, hT.2.1⟩ ⟨hxW, hWy.symm⟩
    have hWa : Γ.Adj W a := (hTW ▸ hT.2.2).symm
    have hNW_eq : N = W :=
      (existsUnique_commonNeighbor hP hya).unique
        ⟨hNy.symm, hNa.symm⟩ ⟨hWy.symm, hWa.symm⟩
    exact hNW hNW_eq
  have hbaM : ¬ Γ.Adj ba M := by
    intro hMba
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLba hMba hLMne
    omega
  have h3ba : Γ.dist ba M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hbaM
      (by rw [hba0, hM]; decide)
  let yb : V := proj hP h3ba
  have hMyb : Γ.Adj M yb := proj_adj hP h3ba
  have hbyb : Γ.dist ba yb = 2 := proj_dist hP h3ba
  have haM : ¬ Γ.Adj a M := by
    intro haM
    have hNM_eq : N = M :=
      (existsUnique_commonNeighbor hP hya).unique
        ⟨hNy.symm, hNa.symm⟩ ⟨hMy.symm, haM⟩
    exact hNM hNM_eq
  have haM3 : Γ.dist a M = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c haM
      (by rw [ha0, hM]; decide)
  have hayb_ne : a ≠ yb := by
    intro hEq
    exact haM (hEq.symm ▸ hMyb).symm
  have hnot2 : Γ.dist a yb ≠ 2 := by
    intro h2
    have hprojY : y = proj hP haM3 :=
      eq_proj hP haM3 hMy (by rw [SimpleGraph.dist_comm]; exact hya)
    have hprojYb : yb = proj hP haM3 := eq_proj hP haM3 hMyb h2
    have hyb_eq_y : yb = y := hprojYb.trans hprojY.symm
    have hba_y : Γ.dist ba y = 2 := by
      rw [← hyb_eq_y]
      exact hbyb
    have hproj_ba : ba = proj hP hyL3 :=
      eq_proj hP hyL3 hLba (by rw [SimpleGraph.dist_comm]; exact hba_y)
    have hproj_x : x = proj hP hyL3 := eq_proj hP hyL3 hLx hyx
    exact hbx (hproj_ba.trans hproj_x.symm)
  have hyb0 : c yb = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMyb
  have hayb : Γ.dist a yb = 4 := by
    rcases dist_eq_two_or_four_of_point_colors hP c ha0 hyb0 hayb_ne with h2 | h4
    · exact absurd h2 hnot2
    · exact h4
  have hxS : x ∈ spanSet Γ a yb :=
    mem_spanSet_of_mem_spanBlock_of_ne hP hT c hH hp hL hM hN hLM hLx hxW hWy hMy
      hz1W hz1y hz2M hz2y hz1z2 hNy hNM hNsub hNa hay hLba hbx hba hMyb hbyb hayb
  have hblocks : ∀ x' : V, Γ.Adj L x' → x' ≠ ba →
      linesThrough Γ ba (spanSet Γ x' yb) = linesThrough Γ ba (spanSet Γ a yb) := by
    intro x' hLx' hx'ne
    have hx'yb : Γ.dist x' yb = 4 :=
      dist_eq_four_of_ne_of_dist_eq_two hP c hL hM hLM hLba hLx' hMyb hbyb hx'ne
    exact linesThrough_spanSet_eq_of_common_L hP hT c (hH ba hba0) hp
      hL hM hLM hLba hLx hLx' hMyb hbyb hba hayb hxS hx'ne hx'yb
  have hsubset : blockThrough Γ ba (spanSet Γ a yb) ⊆ spanUnion hP L M :=
    blockThrough_subset_spanUnion_of_block_eq hP hT c hdeg hL hM hLM hLba hMyb hbyb hblocks
  have hspan : spanOrLine hP a b ⊆ blockThrough Γ ba (spanSet Γ a yb) :=
    spanOrLine_subset_blockThrough hP hT c (hH ba hba0) hp
      hL hM hLM hLba hLx haL hba hMyb hbyb hayb hxS b hLb
  exact subset_trans hspan hsubset

end Main

section PointY

variable {Γ : SimpleGraph V}

theorem spanOrLine_subset_spanUnion_of_eq
    (hP : IsGeneralizedPolygon Γ 4) {L M y b : V}
    (hLb : Γ.Adj L b) (hMy : Γ.Adj M y) :
    spanOrLine hP y b ⊆ spanUnion hP L M := by
  intro u hu
  exact ⟨b, y, hLb, hMy, (spanOrLine_comm hP y b) ▸ hu⟩

end PointY

section Final

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem spanUnion_subset_spanUnion
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {p : ℕ}
    (hp : ∀ a b : V, c a = 0 → Γ.dist a b = 4 → (spanSet Γ a b).ncard = p + 1)
    {s t : ℕ} (hdeg : ∀ v : V, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {L M x W y z1 z2 N : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hxW : Γ.Adj x W) (hWy : Γ.Adj W y) (hMy : Γ.Adj M y)
    (hz1W : Γ.Adj W z1) (hz1y : z1 ≠ y) (hz2M : Γ.Adj M z2) (hz2y : z2 ≠ y)
    (hz1z2 : Γ.dist z1 z2 = 4) (hN : c N = 1)
    (hNsub : Γ.neighborSet N ⊆ spanBlock Γ y z1 z2)
    (hNW : N ≠ W) (hNM : N ≠ M) :
    spanUnion hP N L ⊆ spanUnion hP L M := by
  classical
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMy
  have hNy : Γ.Adj N y := adj_of_neighborSet_subset_spanBlock hP hT c hy0 hN hNsub
  intro u hu
  obtain ⟨a, b, hNa, hLb, huab⟩ := hu
  by_cases hay : a = y
  · subst hay
    exact spanOrLine_subset_spanUnion_of_eq hP hLb hMy huab
  · exact spanOrLine_subset_spanUnion_of_ne hP hT c hH hp hdeg hL hM hLM hLx hxW hWy hMy
      hz1W hz1y hz2M hz2y hz1z2 hN hNy hNW hNM hNsub hNa hLb hay huab

end Final

end CFSG.Geometry.GeneralizedQuadrangles
