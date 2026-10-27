module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Bundles
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Unique

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem inter_eq_of_mem_threeBundle (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsTracePlane Γ c T ∨ IsConePlane Γ c T) {E E' : Set V}
    (hE : E ∈ threeBundle Γ c q T) (hE' : E' ∈ threeBundle Γ c q T) (hne : E ≠ E') :
    E ∩ E' = T := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hEβ : IsThreespace Γ c q E ∧ T ⊆ E := by
    simpa only [threeBundle, Set.mem_setOf_eq] using hE
  have hE'β : IsThreespace Γ c q E' ∧ T ⊆ E' := by
    simpa only [threeBundle, Set.mem_setOf_eq] using hE'
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    by_contra hxT
    have hx0 : c x = 0 := by
      rcases hEβ.1 with ⟨u, -, rfl⟩ | hF
      · exact (mem_ptPerp.mp hx.1).1
      · exact hF.1 x hx.1
    have huniq := existsUnique_threespace hΓ hT hx0 hxT
    exact hne (huniq.unique ⟨hEβ.1, hEβ.2, hx.1⟩ ⟨hE'β.1, hE'β.2, hx.2⟩)
  · intro x hx
    exact ⟨hEβ.2 hx, hE'β.2 hx⟩

theorem inter_eq_of_mem_lineBundle (hΓ : IsThasQuadrangle Γ c q) {L : V} (hL : c L = 1)
    {E E' : Set V} (hE : E ∈ lineBundle Γ c L) (hE' : E' ∈ lineBundle Γ c L)
    (hne : E ≠ E') : E ∩ E' = Γ.neighborSet L := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  obtain ⟨x, hxL, rfl⟩ := hE
  obtain ⟨y, hyL, rfl⟩ := hE'
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hL hyL
  have hxy : x ≠ y := by
    intro h
    exact hne (by rw [h])
  ext z
  constructor
  · rintro ⟨hzx, hzy⟩
    have hz0 : c z = 0 := (mem_ptPerp.mp hzx).1
    have hzxp : Γ.dist z x ≤ 2 := (mem_ptPerp.mp hzx).2 x (by simp)
    have hzyp : Γ.dist z y ≤ 2 := (mem_ptPerp.mp hzy).2 y (by simp)
    by_cases hzx_eq : z = x
    · rw [hzx_eq, mem_neighborSet]
      exact hxL
    by_cases hzy_eq : z = y
    · rw [hzy_eq, mem_neighborSet]
      exact hyL
    have hzx2 : Γ.dist z x = 2 :=
      dist_eq_two_of_le_two_of_ne hP hz0 hx0 hzx_eq hzxp
    have hzy2 : Γ.dist z y = 2 :=
      dist_eq_two_of_le_two_of_ne hP hz0 hy0 hzy_eq hzyp
    by_contra hzL
    have hnot : ¬ Γ.Adj z L := by
      intro h
      rw [mem_neighborSet] at hzL
      exact hzL h.symm
    have hdist : Γ.dist z L = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c hnot (by rw [hz0, hL]; decide)
    exact hxy ((existsUnique_proj hP hdist).unique ⟨hxL, hzx2⟩ ⟨hyL, hzy2⟩)
  · intro hz
    have hzL : Γ.Adj L z := by
      rw [mem_neighborSet] at hz
      exact hz
    have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hzL
    constructor
    · rw [mem_ptPerp]
      refine ⟨hz0, ?_⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      by_cases hzx : z = x
      · rw [hzx]
        simp
      · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hzL.symm hxL hzx)
    · rw [mem_ptPerp]
      refine ⟨hz0, ?_⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      by_cases hzy : z = y
      · rw [hzy]
        simp
      · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hzL.symm hyL hzy)

private theorem cone_line_subset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x y z w : V} (hxy : Γ.dist x y = 4) (hx0 : c x = 0)
    (hz : z ∈ traceSet Γ x y) (hw : w ∈ spanSet Γ x y) (hzw : Γ.dist z w = 2) :
    Γ.neighborSet (commonNeighbor hP hzw) ⊆ ptPerp Γ c {z} ∩ clSet Γ x y := by
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hx0 hz.1
  have hKz : Γ.Adj z (commonNeighbor hP hzw) := commonNeighbor_adj_left hP hzw
  have hKw : Γ.Adj w (commonNeighbor hP hzw) := commonNeighbor_adj_right hP hzw
  have hK1 : c (commonNeighbor hP hzw) = 1 := color_eq_one_of_adj_of_color_eq_zero hz0 hKz
  intro t ht
  have htK : Γ.Adj (commonNeighbor hP hzw) t := by
    rw [mem_neighborSet] at ht
    exact ht
  have ht0 : c t = 0 := color_eq_zero_of_adj_of_color_eq_one hK1 htK
  refine ⟨?_, ?_⟩
  · rw [mem_ptPerp]
    refine ⟨ht0, ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    by_cases htz : t = z
    · rw [htz]
      simp
    · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP htK.symm hKz.symm htz)
  · rw [mem_clSet]
    refine ⟨w, hw, ?_⟩
    by_cases htw : t = w
    · rw [htw]
      simp
    · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP htK.symm hKw.symm htw)

theorem ncard_of_isConePlane (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsConePlane Γ c T) : T.ncard = q ^ 3 + q ^ 2 + 1 := by
  classical
  obtain ⟨x, y, z, hx0, hxy, hztrace, rfl⟩ := hT
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hThick : IsThick Γ := hΓ.thick
  have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hx0 hztrace.1
  let S := {w : V // w ∈ spanSet Γ x y}
  let hzw : ∀ w : S, Γ.dist z w.1 = 2 := fun w => by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_mem_span_of_mem_trace hP hThick hxy w.2 hztrace
  let K : S → V := fun w => commonNeighbor hP (hzw w)
  have hzK : ∀ w : S, Γ.Adj z (K w) := fun w => commonNeighbor_adj_left hP (hzw w)
  have hwK : ∀ w : S, Γ.Adj w.1 (K w) := fun w => commonNeighbor_adj_right hP (hzw w)
  have hKline : ∀ w : S, c (K w) = 1 := fun w =>
    color_eq_one_of_adj_of_color_eq_zero hz0 (hzK w)
  have hzT : z ∈ ptPerp Γ c {z} ∩ clSet Γ x y := by
    refine ⟨?_, ?_⟩
    · rw [mem_ptPerp]
      refine ⟨hz0, ?_⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      simp
    · rw [mem_clSet]
      refine ⟨x, left_mem_spanSet hxy, ?_⟩
      rw [SimpleGraph.dist_comm]
      exact le_of_eq hztrace.1
  let U : Finset V := (Finset.univ : Finset S).biUnion
    (fun w => ((Γ.neighborSet (K w)) \ {z}).toFinset)
  have hUsub : (U : Set V) ⊆ ptPerp Γ c {z} ∩ clSet Γ x y := by
    intro t ht
    rw [Finset.mem_coe, Finset.mem_biUnion] at ht
    obtain ⟨w, -, htw⟩ := ht
    have htw' : t ∈ Γ.neighborSet (K w) \ {z} := by simpa using htw
    exact cone_line_subset hP hThick hxy hx0 hztrace w.2 (hzw w) htw'.1
  have hTsub : ptPerp Γ c {z} ∩ clSet Γ x y ⊆ {z} ∪ (U : Set V) := by
    intro t ht
    by_cases htz : t = z
    · exact Or.inl htz
    · right
      have htperp : t ∈ ptPerp Γ c {z} := ht.1
      have htcl : t ∈ clSet Γ x y := ht.2
      rw [mem_clSet] at htcl
      obtain ⟨w, hwspan, htwle⟩ := htcl
      let wS : S := ⟨w, hwspan⟩
      have ht0 : c t = 0 := (mem_ptPerp.mp htperp).1
      have htz2 : Γ.dist t z = 2 :=
        dist_eq_two_of_le_two_of_ne hP ht0 hz0 htz
          ((mem_ptPerp.mp htperp).2 z (by simp))
      have hw0 : c w = 0 :=
        (color_eq_of_mem_span hP hThick c hxy hwspan).trans hx0
      have htK : Γ.Adj (K wS) t := by
        by_cases htw : t = w
        · rw [htw]
          exact (hwK wS).symm
        · have htw2 : Γ.dist t w = 2 :=
            dist_eq_two_of_le_two_of_ne hP ht0 hw0 htw htwle
          obtain ⟨L, ⟨hLt, hLz, hLw⟩, -⟩ :=
            existsUnique_commonNeighbor_of_pairwise_dist_two hP htz2 htw2 (hzw wS)
          have hLK : L = K wS :=
            (existsUnique_commonNeighbor hP (hzw wS)).unique ⟨hLz, hLw⟩
              ⟨hzK wS, hwK wS⟩
          rw [hLK] at hLt
          exact hLt.symm
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨wS, Finset.mem_univ _, ?_⟩
      simp only [Set.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨htK, htz⟩
  have hTset : ptPerp Γ c {z} ∩ clSet Γ x y = {z} ∪ (U : Set V) := by
    refine Set.Subset.antisymm hTsub ?_
    intro t ht
    rcases ht with hzt | hUt
    · rw [Set.mem_singleton_iff] at hzt
      rw [hzt]
      exact hzT
    · exact hUsub hUt
  have hdisj : Disjoint ({z} : Set V) (U : Set V) := by
    rw [Set.disjoint_left]
    intro t ht hU
    rw [Set.mem_singleton_iff] at ht
    subst t
    rw [Finset.mem_coe, Finset.mem_biUnion] at hU
    obtain ⟨w, -, hwU⟩ := hU
    have hwU' : z ∈ Γ.neighborSet (K w) \ {z} := by simpa using hwU
    exact (Set.notMem_of_mem_sdiff hwU') (by simp)
  have hpair : ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
      (fun w : S => ((Γ.neighborSet (K w)) \ {z}).toFinset) := by
    intro w _ w' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    have ht1 : t ∈ Γ.neighborSet (K w) \ {z} := by simpa using ht
    have ht2 : t ∈ Γ.neighborSet (K w') \ {z} := by simpa using ht'
    have htz : t ≠ z := fun h => (Set.notMem_of_mem_sdiff ht1) (by rw [h]; simp)
    have hww' : w.1 ≠ w'.1 := fun h => hne (Subtype.ext h)
    have hKwne : K w ≠ K w' := by
      intro hKeq
      have h1 : Γ.Adj (K w) w.1 := (hwK w).symm
      have h2 : Γ.Adj (K w) w'.1 := by
        rw [hKeq]
        exact (hwK w').symm
      have h2dist : Γ.dist w.1 w'.1 = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP h1.symm h2 hww'
      have h4dist : Γ.dist w.1 w'.1 = 4 :=
        dist_eq_four_of_mem_span hP hThick hxy w.2 w'.2 hww'
      omega
    have hKwt : Γ.Adj (K w) t := by
      have hmem : t ∈ Γ.neighborSet (K w) := Set.mem_of_mem_sdiff ht1
      rw [mem_neighborSet] at hmem
      exact hmem
    have hKw't : Γ.Adj (K w') t := by
      have hmem : t ∈ Γ.neighborSet (K w') := Set.mem_of_mem_sdiff ht2
      rw [mem_neighborSet] at hmem
      exact hmem
    exact hKwne (eq_of_two_common_points hP htz hKwt (hzK w).symm hKw't (hzK w').symm)
  have hLdiffcard : ∀ w : S, ((Γ.neighborSet (K w)) \ {z}).ncard = q ^ 2 := by
    intro w
    have hzsub : ({z} : Set V) ⊆ Γ.neighborSet (K w) := by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      rw [mem_neighborSet]
      exact (hzK w).symm
    have hLcard : (Γ.neighborSet (K w)).ncard = q ^ 2 + 1 := by
      rw [SimpleGraph.ncard_neighborSet, hΓ.deg (K w), if_neg (by rw [hKline w]; decide)]
    rw [Set.ncard_sdiff hzsub, hLcard, Set.ncard_singleton]
    omega
  have hUcard : U.card = Fintype.card S * q ^ 2 := by
    rw [Finset.card_biUnion hpair]
    have hterm : ∀ w : S, ((Γ.neighborSet (K w)) \ {z}).toFinset.card = q ^ 2 := by
      intro w
      rw [← Set.ncard_eq_toFinset_card' ((Γ.neighborSet (K w)) \ {z})]
      exact hLdiffcard w
    rw [Finset.sum_congr rfl (fun w _ => hterm w), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have hScard : Fintype.card S = q + 1 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ↥(spanSet Γ x y) = q + 1
    rw [Nat.card_coe_set_eq]
    exact hΓ.span x y hx0 hxy
  rw [hTset, Set.ncard_union_eq hdisj, Set.ncard_singleton, Set.ncard_coe_finset, hUcard,
    hScard]
  ring

theorem ncard_abs_threeBundle (hΓ : IsThasQuadrangle Γ c q) {T : Set V}
    (hT : IsTracePlane Γ c T) :
    {E | E ∈ threeBundle Γ c q T ∧ ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard = q + 1 := by
  classical
  obtain ⟨y, z, hy0, hyz, rfl⟩ := hT
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hThick : IsThick Γ := hΓ.thick
  have hset : {E | E ∈ threeBundle Γ c q (traceSet Γ y z) ∧
      ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}} =
      (fun u => ptPerp Γ c {u}) '' (spanSet Γ y z) := by
    ext E
    constructor
    · rintro ⟨hE, u, hu0, rfl⟩
      have hEβ : IsThreespace Γ c q (ptPerp Γ c {u}) ∧ traceSet Γ y z ⊆ ptPerp Γ c {u} := by
        simpa only [threeBundle, Set.mem_setOf_eq] using hE
      refine ⟨u, ?_, rfl⟩
      rw [mem_spanSet]
      intro t ht
      simpa [SimpleGraph.dist_comm] using (mem_ptPerp.mp (hEβ.2 ht)).2 u (by simp)
    · rintro ⟨u, hu, rfl⟩
      have hu0 : c u = 0 := (color_eq_of_mem_span hP hThick c hyz hu).trans hy0
      refine ⟨⟨Or.inl ⟨u, hu0, rfl⟩, ?_⟩, u, hu0, rfl⟩
      intro t ht
      rw [mem_ptPerp]
      exact ⟨color_eq_zero_of_dist_eq_two hP hy0 ht.1, by
        simpa [SimpleGraph.dist_comm] using hu t ht⟩
  rw [hset]
  have hinj : Set.InjOn (fun u => ptPerp Γ c {u}) (spanSet Γ y z) := by
    intro u hu v hv huv
    have hu0 : c u = 0 := (color_eq_of_mem_span hP hThick c hyz hu).trans hy0
    have hv0 : c v = 0 := (color_eq_of_mem_span hP hThick c hyz hv).trans hy0
    exact ptPerp_singleton_injective hP hThick hu0 hv0 huv
  rw [hinj.ncard_image]
  exact hΓ.span y z hy0 hyz

end CFSG.Geometry.GeneralizedQuadrangles
