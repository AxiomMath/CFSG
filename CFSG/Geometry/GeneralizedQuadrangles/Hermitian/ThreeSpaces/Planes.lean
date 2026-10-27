module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.SubquadranglePlanes
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

private theorem neighborSet_subset_of_two_mem (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hF : IsFullSubquadrangle c E q) {L a b : V} (haL : Γ.Adj L a) (hbL : Γ.Adj L b)
    (haE : a ∈ E) (hbE : b ∈ E) (hab : a ≠ b) : Γ.neighborSet L ⊆ E := by
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero (hF.1 a haE) haL.symm
  have h2 : 2 ≤ (Γ.neighborSet L ∩ E).ncard := by
    have h1' : 1 < (Γ.neighborSet L ∩ E).ncard :=
      (Set.one_lt_ncard (s := Γ.neighborSet L ∩ E)).mpr
        ⟨a, ⟨haL, haE⟩, b, ⟨hbL, hbE⟩, hab⟩
    omega
  exact hF.2.1 L hL1 h2

private theorem cone_eq_of_isFullSubquadrangle (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hF : IsFullSubquadrangle c E q) {x y z : V} (hxE : x ∈ E) (hyE : y ∈ E)
    (hzE : z ∈ E) (hxy : Γ.dist x y = 4) (hzx : Γ.dist z x = 2)
    (hzy : Γ.dist z y = 2) :
    ptPerp Γ c {z} ∩ clSet Γ x y = ptPerp Γ c {z} ∩ E := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hx0 : c x = 0 := hF.1 x hxE
  have hz0 : c z = 0 := hF.1 z hzE
  have hztrace : z ∈ traceSet Γ x y :=
    ⟨by rw [SimpleGraph.dist_comm]; exact hzx, by rw [SimpleGraph.dist_comm]; exact hzy⟩
  have hspanE : spanSet Γ x y ⊆ E :=
    spanSet_subset_of_isFullSubquadrangle hΓ hF hxE hyE hxy
  have hspan0 : ∀ v ∈ spanSet Γ x y, c v = 0 := fun v hv =>
    (color_eq_of_mem_span hP hT c hxy hv).trans hx0
  have hznotspan : z ∉ spanSet Γ x y :=
    not_mem_spanSet_of_mem_traceSet hP hT hxy hztrace
  refine Set.Subset.antisymm ?_ ?_
  · rintro w ⟨hwperp, hwcl⟩
    refine ⟨hwperp, ?_⟩
    have hw0 : c w = 0 := hwperp.1
    by_cases hwz : w = z
    · rwa [hwz]
    have hzw : Γ.dist z w = 2 :=
      dist_eq_two_of_le_two_of_ne hP hz0 hw0 (Ne.symm hwz) (by
        have h := (mem_ptPerp.mp hwperp).2 z (by simp)
        rwa [SimpleGraph.dist_comm] at h)
    obtain ⟨v, hvspan, hwv⟩ := hwcl
    have hv0 : c v = 0 := hspan0 v hvspan
    have hvE : v ∈ E := hspanE hvspan
    by_cases hwv_eq : w = v
    · simpa [hwv_eq] using hvE
    have hwv2 : Γ.dist w v = 2 :=
      dist_eq_two_of_le_two_of_ne hP hw0 hv0 hwv_eq hwv
    have hzv2 : Γ.dist z v = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hvspan hztrace
    obtain ⟨L, hLz, hLw, hLv⟩ :=
      (existsUnique_commonNeighbor_of_pairwise_dist_two hP hzw hzv2 hwv2).exists
    have hzvne : z ≠ v := fun h => hznotspan (h ▸ hvspan)
    have hfull := neighborSet_subset_of_two_mem hΓ hF hLz.symm hLv.symm hzE hvE hzvne
    exact hfull hLw.symm
  · rintro w ⟨hwperp, hwE⟩
    refine ⟨hwperp, ?_⟩
    have hw0 : c w = 0 := hwperp.1
    by_cases hwz : w = z
    · refine ⟨x, left_mem_spanSet hxy, ?_⟩
      rw [hwz]
      exact le_of_eq hzx
    have hzw2 : Γ.dist z w = 2 :=
      dist_eq_two_of_le_two_of_ne hP hz0 hw0 (Ne.symm hwz) (by
        have h := (mem_ptPerp.mp hwperp).2 z (by simp)
        rwa [SimpleGraph.dist_comm] at h)
    have hzwne : z ≠ w := Ne.symm hwz
    have hSsub : linesThrough Γ z (spanSet Γ x y) ⊆
        {L | Γ.Adj z L ∧ Γ.neighborSet L ⊆ E} := by
      intro L hL
      rw [mem_linesThrough] at hL
      obtain ⟨hzL, v, hvspan, hLv⟩ := hL
      refine ⟨hzL, neighborSet_subset_of_two_mem hΓ hF hzL.symm hLv hzE (hspanE hvspan) ?_⟩
      intro hzv
      exact hznotspan (hzv ▸ hvspan)
    have hScard : (linesThrough Γ z (spanSet Γ x y)).ncard = q + 1 := by
      rw [ncard_linesThrough_spanSet hP hT hzx hzy hxy, hΓ.span x y hx0 hxy]
    have hFcard : {L | Γ.Adj z L ∧ Γ.neighborSet L ⊆ E}.ncard = q + 1 :=
      hF.2.2.1 z hzE
    have hS_eq : linesThrough Γ z (spanSet Γ x y) =
        {L | Γ.Adj z L ∧ Γ.neighborSet L ⊆ E} :=
      Set.eq_of_subset_of_ncard_le hSsub (by rw [hScard, hFcard])
    have hLmem : commonNeighbor hP hzw2 ∈ {L | Γ.Adj z L ∧ Γ.neighborSet L ⊆ E} :=
      ⟨commonNeighbor_adj_left hP hzw2,
        neighborSet_subset_of_two_mem hΓ hF (commonNeighbor_adj_left hP hzw2).symm
          (commonNeighbor_adj_right hP hzw2).symm hzE hwE hzwne⟩
    have hLmem' : commonNeighbor hP hzw2 ∈ linesThrough Γ z (spanSet Γ x y) :=
      hS_eq.symm ▸ hLmem
    rw [mem_linesThrough] at hLmem'
    obtain ⟨-, v, hvspan, hLv⟩ := hLmem'
    refine ⟨v, hvspan, ?_⟩
    have h1 : Γ.dist w (commonNeighbor hP hzw2) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (commonNeighbor_adj_right hP hzw2)
    have h2 : Γ.dist (commonNeighbor hP hzw2) v = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hLv
    have htri := hP.connected.dist_triangle (u := w) (v := commonNeighbor hP hzw2) (w := v)
    omega

private theorem exists_opposite_pair_of_mem (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hF : IsFullSubquadrangle c E q) {u : V} (huE : u ∈ E) :
    ∃ x y, x ∈ E ∧ y ∈ E ∧ Γ.dist x y = 4 ∧ u ∈ traceSet Γ x y := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hu0 : c u = 0 := hF.1 u huE
  have hcard : {L | Γ.Adj u L ∧ Γ.neighborSet L ⊆ E}.ncard = q + 1 := hF.2.2.1 u huE
  have hq : 2 ≤ q := hΓ.two_le
  have h1 : 1 < {L | Γ.Adj u L ∧ Γ.neighborSet L ⊆ E}.ncard := by rw [hcard]; omega
  obtain ⟨L1, hL1, L2, hL2, hL12⟩ :=
    (Set.one_lt_ncard (s := {L | Γ.Adj u L ∧ Γ.neighborSet L ⊆ E})).mp h1
  have huL1 : Γ.Adj u L1 := hL1.1
  have hL1full : Γ.neighborSet L1 ⊆ E := hL1.2
  have huL2 : Γ.Adj u L2 := hL2.1
  have hL2full : Γ.neighborSet L2 ⊆ E := hL2.2
  have hL11 : c L1 = 1 := color_eq_one_of_adj_of_color_eq_zero hu0 huL1
  have hL21 : c L2 = 1 := color_eq_one_of_adj_of_color_eq_zero hu0 huL2
  have hN1 : 1 < (Γ.neighborSet L1).ncard := by
    rw [SimpleGraph.ncard_neighborSet, hΓ.deg L1, if_neg (by rw [hL11]; decide)]
    nlinarith [hq]
  obtain ⟨x, hxN1, hxu⟩ := Set.exists_ne_of_one_lt_ncard hN1 u
  have hN2 : 1 < (Γ.neighborSet L2).ncard := by
    rw [SimpleGraph.ncard_neighborSet, hΓ.deg L2, if_neg (by rw [hL21]; decide)]
    nlinarith [hq]
  obtain ⟨y, hyN2, hyu⟩ := Set.exists_ne_of_one_lt_ncard hN2 u
  have hxE : x ∈ E := hL1full hxN1
  have hyE : y ∈ E := hL2full hyN2
  have hux : Γ.dist u x = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP huL1 hxN1 hxu.symm
  have huy : Γ.dist u y = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP huL2 hyN2 hyu.symm
  have hc1 : commonNeighbor hP hux = L1 :=
    (eq_commonNeighbor hP hux huL1 hxN1.symm).symm
  have hc2 : commonNeighbor hP huy = L2 :=
    (eq_commonNeighbor hP huy huL2 hyN2.symm).symm
  have hxy : Γ.dist x y = 4 :=
    dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hux huy (by
      rw [hc1, hc2]
      exact hL12)
  refine ⟨x, y, hxE, hyE, hxy, ?_⟩
  exact ⟨by rw [SimpleGraph.dist_comm]; exact hux, by rw [SimpleGraph.dist_comm]; exact huy⟩

private theorem mem_E_of_mem_val_image {E : Set V} (hF : IsFullSubquadrangle c E q)
    {X : Set (subquadrangleSet Γ c E)} {v : V}
    (hv : v ∈ Subtype.val '' X) (hv0 : c v = 0) : v ∈ E := by
  obtain ⟨a, -, rfl⟩ := hv
  rcases mem_subquadrangleSet.mp a.2 with h | h
  · exact h
  · exact absurd ((mem_subquadrangleLines.mp h).1) (by rw [hv0]; decide)

theorem isStarPlane_subquadrangle_iff (hΓ : IsThasQuadrangle Γ c q) {E : Set V}
    (hE : IsFullSubquadrangle c E q) {X : Set (subquadrangleSet Γ c E)} :
    IsStarPlane (Γ.induce (subquadrangleSet Γ c E)) (subquadrangleColoring c E) X ↔
      IsTracePlane Γ c (Subtype.val '' X) ∨ IsConePlane Γ c (Subtype.val '' X) := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hP' : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c E)) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hE
  have hT' : IsThick (Γ.induce (subquadrangleSet Γ c E)) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hE hΓ.two_le
  have hdeg' : ∀ w : subquadrangleSet Γ c E,
      (Γ.induce (subquadrangleSet Γ c E)).degree w =
        if subquadrangleColoring c E w = 0 then q + 1 else q ^ 2 + 1 :=
    fun w => degree_subquadrangleGraph hΓ hE w
  have hreg' : ∀ w : subquadrangleSet Γ c E, subquadrangleColoring c E w = 0 →
      IsRegularVertex (Γ.induce (subquadrangleSet Γ c E)) w :=
    fun w hw => isRegularVertex_subquadrangle hΓ hE w hw
  constructor
  · intro hX
    rcases isStarPlane_cases hP' hT' (subquadrangleColoring c E) (s := q ^ 2) (t := q)
      hdeg' hreg' hX with habs | hnon
    · rw [isAbsPlane_subquadrangle_iff hΓ hE] at habs
      obtain ⟨u, huE, hval⟩ := habs
      obtain ⟨x, y, hxE, hyE, hxy, hutrace⟩ := exists_opposite_pair_of_mem hΓ hE huE
      refine Or.inr ⟨x, y, u, hE.1 x hxE, hxy, hutrace, ?_⟩
      rw [hval, cone_eq_of_isFullSubquadrangle hΓ hE hxE hyE huE hxy
        (by rw [SimpleGraph.dist_comm]; exact hutrace.1)
        (by rw [SimpleGraph.dist_comm]; exact hutrace.2)]
    · rw [isNonabsPlane_subquadrangle_iff hΓ hE] at hnon
      obtain ⟨y, z, hy0, hyz, -, hval⟩ := hnon
      exact Or.inl ⟨y, z, hy0, hyz, hval⟩
  · rintro (⟨y, z, hy0, hyz, hval⟩ | ⟨x, y, z, hx0, hxy, hztrace, hval⟩)
    · have hTP : traceSet Γ y z ⊆ E := by
        intro w hw
        have hw' : w ∈ Subtype.val '' X := by rw [hval]; exact hw
        exact mem_E_of_mem_val_image hE hw' (color_eq_zero_of_dist_eq_two hP hy0 hw.1)
      exact ((isNonabsPlane_subquadrangle_iff hΓ hE).mpr
        ⟨y, z, hy0, hyz, hTP, hval⟩).1
    · have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hx0 hztrace.1
      have hzT : z ∈ ptPerp Γ c {z} ∩ clSet Γ x y := by
        refine ⟨⟨hz0, ?_⟩, x, left_mem_spanSet hxy, ?_⟩
        · intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst w
          simp
        · rw [SimpleGraph.dist_comm]
          exact le_of_eq hztrace.1
      have hzImage : z ∈ Subtype.val '' X := by rw [hval]; exact hzT
      have hzE : z ∈ E := mem_E_of_mem_val_image hE hzImage hz0
      have hspanT : spanSet Γ x y ⊆ ptPerp Γ c {z} ∩ clSet Γ x y := by
        intro v hv
        have hv0 : c v = 0 := (color_eq_of_mem_span hP hT c hxy hv).trans hx0
        refine ⟨⟨hv0, ?_⟩, v, hv, by simp⟩
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst w
        have h := spanSet_subset_perpSet (x := x) (y := y) (u := z) hztrace hv
        simpa [mem_perpSet, SimpleGraph.dist_comm] using h
      have hxE : x ∈ E := mem_E_of_mem_val_image hE (by
        rw [hval]; exact hspanT (left_mem_spanSet hxy))
        ((color_eq_of_mem_span hP hT c hxy (left_mem_spanSet hxy)).trans hx0)
      have hyE : y ∈ E := mem_E_of_mem_val_image hE (by
        rw [hval]; exact hspanT (right_mem_spanSet hxy))
        ((color_eq_of_mem_span hP hT c hxy (right_mem_spanSet hxy)).trans hx0)
      have hcone := cone_eq_of_isFullSubquadrangle hΓ hE hxE hyE hzE hxy
        (by rw [SimpleGraph.dist_comm]; exact hztrace.1)
        (by rw [SimpleGraph.dist_comm]; exact hztrace.2)
      let z' : subquadrangleSet Γ c E := ⟨z, mem_subquadrangleSet.mpr (Or.inl hzE)⟩
      have hz'0 : subquadrangleColoring c E z' = 0 := by
        rw [subquadrangleColoring_apply]
        exact hz0
      have hpt : Subtype.val '' ptPerp (Γ.induce (subquadrangleSet Γ c E))
          (subquadrangleColoring c E) {z'} = ptPerp Γ c {z} ∩ E := by
        rw [ptPerp_subquadrangle hΓ hE,
          show Subtype.val '' ({z'} : Set (subquadrangleSet Γ c E)) = {z} from by
            ext w
            simp [z']]
      have hXeq : X = ptPerp (Γ.induce (subquadrangleSet Γ c E))
          (subquadrangleColoring c E) {z'} := by
        refine (Set.image_eq_image Subtype.val_injective).mp ?_
        rw [hval, hcone, hpt]
      rw [hXeq]
      exact isStarPlane_ptPerp_singleton hP' hT' (subquadrangleColoring c E)
        (s := q ^ 2) (t := q) hdeg' hz'0

end CFSG.Geometry.GeneralizedQuadrangles
