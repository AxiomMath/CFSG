module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.PlanesThrough2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section Vocabulary

variable (Γ : SimpleGraph V) (c : Γ.Coloring (Fin 2))

@[expose] def conjLine (X : Set V) (p : V) : Set V :=
  ptPerp Γ c (ptPerp Γ c {p} ∩ X)

@[expose] def IsConjPlane (X Y : Set V) : Prop :=
  ∃ L, IsStarLine Γ c L ∧ L ⊆ X ∧ ptPerp Γ c L ⊆ Y

@[expose] def conjNet (X : Set V) : Set (Set V) :=
  {Y | IsStarPlane Γ c Y ∧ IsConjPlane Γ c X Y}

@[expose] def conjBundle (β : Set (Set V)) : Set (Set V) :=
  {Y | IsStarPlane Γ c Y ∧ ∀ X ∈ β, IsConjPlane Γ c Y X}

end Vocabulary

section Aux

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ptPerp_neighborSet_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {K : V} (hK : c K = 1) :
    ptPerp Γ c (Γ.neighborSet K) = Γ.neighborSet K := by
  classical
  ext z
  constructor
  · intro hz
    rw [mem_ptPerp] at hz
    have hz0 : c z = 0 := hz.1
    by_contra hzK
    have hdist3 : Γ.dist z K = 3 :=
      dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hzK h.symm) (by
        rw [hz0, hK]
        decide)
    obtain ⟨u, hu, huniq⟩ := existsUnique_proj_of_not_adj hP hz0 hK
      (fun h => hzK h.symm)
    have hNcard : 1 < (Γ.neighborSet K).ncard := by
      rw [SimpleGraph.ncard_neighborSet]
      have h3 := hT K
      omega
    obtain ⟨v, hv, hvu⟩ := Set.exists_ne_of_one_lt_ncard hNcard u
    have hv0 : c v = 0 := color_eq_zero_of_adj_of_color_eq_one hK hv
    have hzv_le : Γ.dist z v ≤ 2 := hz.2 v hv
    have hzv_ne : z ≠ v := by
      intro h
      exact hzK (h ▸ hv)
    have hzv : Γ.dist z v = 2 := dist_eq_two_of_le_two_of_ne hP hz0 hv0 hzv_ne hzv_le
    exact hvu (huniq v ⟨hv, hzv⟩)
  · intro hz
    rw [mem_ptPerp]
    refine ⟨color_eq_zero_of_adj_of_color_eq_one hK hz, ?_⟩
    intro w hw
    by_cases hzw : z = w
    · rw [hzw]
      simp
    · exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hz.symm hw hzw)

theorem eq_of_adj_of_adj_of_adj (hP : IsGeneralizedPolygon Γ 4) {L M v w : V}
    (hLv : Γ.Adj L v) (hMv : Γ.Adj M v) (hLw : Γ.Adj L w) (hMw : Γ.Adj M w)
    (hvw : v ≠ w) : L = M := by
  have hdist : Γ.dist w v = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hLw.symm hLv hvw.symm
  have hLw1 : Γ.dist w L = 1 := by
    rw [SimpleGraph.dist_comm]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr hLw
  have hMw1 : Γ.dist w M = 1 := by
    rw [SimpleGraph.dist_comm]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr hMw
  have h1 : Γ.dist w L + 1 = Γ.dist w v := by rw [hLw1]; omega
  have h2 : Γ.dist w M + 1 = Γ.dist w v := by rw [hMw1]; omega
  exact hP.eq_of_adj_of_dist_succ (y := w) (v := v) (by rw [hdist]; norm_num)
    hLv.symm hMv.symm h1 h2

theorem isStarLine_neighborSet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {K : V} (hK : c K = 1) :
    IsStarLine Γ c (Γ.neighborSet K) := by
  classical
  have hNcard : 3 ≤ (Γ.neighborSet K).ncard := by
    rw [SimpleGraph.ncard_neighborSet]
    exact hT K
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (Set.one_lt_ncard (s := Γ.neighborSet K)).mp
      (by omega : 1 < (Γ.neighborSet K).ncard)
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hK hx
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hK hy
  have hdist : Γ.dist x y = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hx.symm hy hxy
  have hcommon : commonNeighbor hP hdist = K :=
    (eq_commonNeighbor hP hdist hx.symm hy.symm).symm
  refine ⟨x, y, hx0, hy0, hxy, ?_⟩
  rw [starLine_eq_neighborSet hP hT c hx0 hdist, hcommon]

theorem isHypLine_of_isStarLine_not_ordinary (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {L : Set V} (hL : IsStarLine Γ c L)
    (hnot : ¬ ∃ K, c K = 1 ∧ L = Γ.neighborSet K) : IsHypLine Γ c L := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hL
  rcases dist_eq_two_or_four_of_color_zero hP hx hy hxy with h2 | h4
  · exfalso
    refine hnot ⟨commonNeighbor hP h2,
      color_eq_one_of_adj_of_color_eq_zero hx (commonNeighbor_adj_left hP h2), ?_⟩
    exact starLine_eq_neighborSet hP hT c hx h2
  · exact ⟨x, y, hx, h4, rfl⟩

theorem isHypLine_ptPerp (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {L : Set V}
    (hL : IsHypLine Γ c L) : IsHypLine Γ c (ptPerp Γ c L) := by
  classical
  obtain ⟨x, y, hx, hxy4, rfl⟩ := hL
  have hstar : IsStarLine Γ c (starLine Γ c x y) :=
    IsHypLine.isStarLine hP ⟨x, y, hx, hxy4, rfl⟩
  have hperpstar : IsStarLine Γ c (ptPerp Γ c (starLine Γ c x y)) :=
    (ptPerp_ptPerp_starLine hP hT c hdeg hreg hstar).1
  have htrace : ptPerp Γ c (starLine Γ c x y) = traceSet Γ x y :=
    ptPerp_starLine_eq_traceSet hP hT c hx hxy4
  have htrace_card : (traceSet Γ x y).ncard = t + 1 := by
    rw [ncard_trace hP hxy4, hdeg x, if_pos hx]
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have h2 : 1 < (traceSet Γ x y).ncard := by
    rw [htrace_card]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := (Set.one_lt_ncard (s := traceSet Γ x y)).mp h2
  have hu0 : c u = 0 := color_eq_zero_of_dist_eq_two hP hx hu.1
  have huv4 : Γ.dist u v = 4 := dist_eq_four_of_mem_trace hP hxy4 hu hv huv
  have hEq : ptPerp Γ c (starLine Γ c x y) = starLine Γ c u v :=
    starLine_eq_of_isStarLine_of_mem hP hT hperpstar
      (by rwa [htrace]) (by rwa [htrace]) huv
  exact ⟨u, v, hu0, huv4, hEq⟩

theorem not_isNonabsPlane_of_isAbsPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {X : Set V}
    (hX : IsAbsPlane Γ c X) : ¬ IsNonabsPlane Γ c X := by
  rintro ⟨-, hO⟩
  obtain ⟨u, hu, rfl⟩ := hX
  obtain ⟨L, hLu⟩ := exists_adj_of_color_zero hT hu
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hu hLu
  have hsub : Γ.neighborSet L ⊆ ptPerp Γ c {u} := neighborSet_subset_ptPerp hP hL1 hLu
  have h1 := hO.2 L hL1
  rw [Set.inter_eq_left.mpr hsub] at h1
  have hNcard : (Γ.neighborSet L).ncard = s + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg L, if_neg (by rw [hL1]; decide)]
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  omega

theorem one_lt_ncard_of_isStarPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V}
    (hX : IsStarPlane Γ c X) : 1 < X.ncard := by
  classical
  rcases isStarPlane_cases hP hT c hdeg hreg hX with habs | hnon
  · obtain ⟨u, hu, rfl⟩ := habs
    rw [ncard_ptPerp_singleton hP hT c hdeg hu]
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have ht : 2 ≤ t := two_le_t hP hT c hdeg
    nlinarith
  · rw [ncard_of_isOvoid hP hT c hdeg hnon.2]
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    have ht : 2 ≤ t := two_le_t hP hT c hdeg
    nlinarith

end Aux

section ConjugacyD

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem ncard_inter_ptPerp_singleton_of_isStarPlane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {p : V} (hp : c p = 0) (hpX : p ∉ X) :
    (ptPerp Γ c {p} ∩ X).ncard = t + 1 := by
  classical
  rw [Set.inter_comm]
  rcases isStarPlane_cases hP hT c hdeg hreg hX with habs | hnon
  · obtain ⟨u, hu, rfl⟩ := habs
    have hp_ne_u : p ≠ u := by
      intro h
      apply hpX
      rw [h]
      rw [mem_ptPerp]
      refine ⟨hu, ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      simp
    have hpu4 : Γ.dist p u = 4 := by
      have hnotle : ¬ Γ.dist p u ≤ 2 := by
        intro hle
        apply hpX
        rw [mem_ptPerp]
        refine ⟨hp, ?_⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hle
      rcases dist_eq_two_or_four_of_color_zero hP hp hu hp_ne_u with h2 | h4
      · omega
      · exact h4
    have hEq : ptPerp Γ c {u} ∩ ptPerp Γ c {p} = traceSet Γ p u := by
      ext z
      constructor
      · rintro ⟨hzu, hzp⟩
        have hz0 : c z = 0 := (mem_ptPerp.mp hzp).1
        have hzp_le : Γ.dist z p ≤ 2 := (mem_ptPerp.mp hzp).2 p (by simp)
        have hzu_le : Γ.dist z u ≤ 2 := (mem_ptPerp.mp hzu).2 u (by simp)
        have hzp_ne : z ≠ p := by
          intro h
          rw [h] at hzu_le
          omega
        have hzu_ne : z ≠ u := by
          intro h
          rw [h] at hzp_le
          have hpu4' : Γ.dist u p = 4 := by rwa [SimpleGraph.dist_comm]
          omega
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_le_two_of_ne hP hz0 hp hzp_ne hzp_le
        · rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_le_two_of_ne hP hz0 hu hzu_ne hzu_le
      · intro hz
        rw [mem_traceSet] at hz
        have hz0 : c z = 0 := color_eq_zero_of_dist_eq_two hP hp hz.1
        refine ⟨?_, ?_⟩
        · rw [mem_ptPerp]
          refine ⟨hz0, ?_⟩
          intro z' hz'
          rw [Set.mem_singleton_iff] at hz'
          subst z'
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hz.2
        · rw [mem_ptPerp]
          refine ⟨hz0, ?_⟩
          intro z' hz'
          rw [Set.mem_singleton_iff] at hz'
          subst z'
          rw [SimpleGraph.dist_comm]
          exact le_of_eq hz.1
    rw [hEq, ncard_trace hP hpu4, hdeg p, if_pos hp]
  · exact ncard_inter_ovoid_ptPerp hP hT c hdeg hnon.2 hp hpX

theorem isStarLine_inter_ptPerp_singleton_of_isStarPlane (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {p : V} (hp : c p = 0) (hpX : p ∉ X) :
    IsStarLine Γ c (ptPerp Γ c {p} ∩ X) := by
  classical
  have hY : IsStarPlane Γ c (ptPerp Γ c {p}) := isStarPlane_ptPerp_singleton hP hT c hdeg hp
  have hXY : X ≠ ptPerp Γ c {p} := by
    intro h
    apply hpX
    rw [h]
    rw [mem_ptPerp]
    refine ⟨hp, ?_⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    simp
  have hcard := ncard_inter_ptPerp_singleton_of_isStarPlane hP hT c hdeg hreg hX hp hpX
  rcases inter_cases hP hT c hdeg hreg hX hY hXY with hzero | hsingle | hline
  · exfalso
    have hzero' : ptPerp Γ c {p} ∩ X = ∅ := by rw [Set.inter_comm]; exact hzero
    rw [hzero'] at hcard
    simp at hcard
  · obtain ⟨x, hx⟩ := hsingle
    exfalso
    have hsingle' : ptPerp Γ c {p} ∩ X = {x} := by rw [Set.inter_comm]; exact hx
    rw [hsingle'] at hcard
    simp at hcard
    have ht : 2 ≤ t := two_le_t hP hT c hdeg
    omega
  · simpa [Set.inter_comm] using hline

theorem isHypLine_conjLine (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {p : V} (hp : c p = 0) (hpX : p ∉ X) :
    IsHypLine Γ c (conjLine Γ c X p) ∧ p ∈ conjLine Γ c X p ∧
      ptPerp Γ c (conjLine Γ c X p) ⊆ X := by
  classical
  let M : Set V := ptPerp Γ c {p} ∩ X
  have hMstar : IsStarLine Γ c M :=
    isStarLine_inter_ptPerp_singleton_of_isStarPlane hP hT c hdeg hreg hX hp hpX
  have hMcard : M.ncard = t + 1 :=
    ncard_inter_ptPerp_singleton_of_isStarPlane hP hT c hdeg hreg hX hp hpX
  have hpM : p ∉ M := fun h => hpX h.2
  have hMnot : ¬ ∃ K, c K = 1 ∧ M = Γ.neighborSet K := by
    rintro ⟨K, hK, hMK⟩
    have hnotAdj : ¬ Γ.Adj p K := by
      intro hAdj
      exact hpM (by rw [hMK]; exact hAdj.symm)
    obtain ⟨u, hu, huniq⟩ := existsUnique_proj_of_not_adj hP hp hK hnotAdj
    have h2 : 1 < M.ncard := by
      rw [hMcard]
      have ht : 2 ≤ t := two_le_t hP hT c hdeg
      omega
    obtain ⟨a, haM, b, hbM, hab⟩ := (Set.one_lt_ncard (s := M)).mp h2
    have haAdj : Γ.Adj K a := by simpa [hMK] using haM
    have hbAdj : Γ.Adj K b := by simpa [hMK] using hbM
    have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hK haAdj
    have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hK hbAdj
    have hpa_le : Γ.dist p a ≤ 2 := by
      have h := (mem_ptPerp.mp haM.1).2 p (by simp)
      rwa [SimpleGraph.dist_comm] at h
    have hpb_le : Γ.dist p b ≤ 2 := by
      have h := (mem_ptPerp.mp hbM.1).2 p (by simp)
      rwa [SimpleGraph.dist_comm] at h
    have hpa_ne : p ≠ a := fun h => hpM (h ▸ haM)
    have hpb_ne : p ≠ b := fun h => hpM (h ▸ hbM)
    have hpa : Γ.dist p a = 2 :=
      dist_eq_two_of_le_two_of_ne hP hp ha0 hpa_ne hpa_le
    have hpb : Γ.dist p b = 2 :=
      dist_eq_two_of_le_two_of_ne hP hp hb0 hpb_ne hpb_le
    have ha_eq : a = u := huniq a ⟨haAdj, hpa⟩
    have hb_eq : b = u := huniq b ⟨hbAdj, hpb⟩
    exact hab (ha_eq.trans hb_eq.symm)
  have hMhyp : IsHypLine Γ c M :=
    isHypLine_of_isStarLine_not_ordinary hP hT c hMstar hMnot
  have hNhyp : IsHypLine Γ c (conjLine Γ c X p) := by
    change IsHypLine Γ c (ptPerp Γ c M)
    exact isHypLine_ptPerp hP hT c hdeg hreg hMhyp
  refine ⟨hNhyp, ?_, ?_⟩
  · change p ∈ ptPerp Γ c M
    rw [mem_ptPerp]
    refine ⟨hp, ?_⟩
    intro m hm
    have h := (mem_ptPerp.mp hm.1).2 p (Set.mem_singleton p)
    rwa [SimpleGraph.dist_comm] at h
  · change ptPerp Γ c (ptPerp Γ c M) ⊆ X
    rw [(ptPerp_ptPerp_starLine hP hT c hdeg hreg hMstar).2]
    exact Set.inter_subset_right

theorem eq_conjLine (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {p : V} (hpX : p ∉ X) {L : Set V} (hL : IsStarLine Γ c L) (hpL : p ∈ L)
    (hLX : ptPerp Γ c L ⊆ X) : L = conjLine Γ c X p := by
  classical
  have hp : c p = 0 := by
    obtain ⟨x, y, hx, hy, hxy, hLxy⟩ := hL
    have hpL' : p ∈ starLine Γ c x y := by rwa [hLxy] at hpL
    exact color_eq_zero_of_mem_starLine hpL'
  let M : Set V := ptPerp Γ c {p} ∩ X
  have hMstar : IsStarLine Γ c M :=
    isStarLine_inter_ptPerp_singleton_of_isStarPlane hP hT c hdeg hreg hX hp hpX
  have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).1
  have hMhyp : IsHypLine Γ c M := by
    have htemp : IsHypLine Γ c (ptPerp Γ c (conjLine Γ c X p)) :=
      isHypLine_ptPerp hP hT c hdeg hreg hNhyp
    change IsHypLine Γ c (ptPerp Γ c (ptPerp Γ c M)) at htemp
    rwa [(ptPerp_ptPerp_starLine hP hT c hdeg hreg hMstar).2] at htemp
  have hLnot : ¬ ∃ K, c K = 1 ∧ L = Γ.neighborSet K := by
    rintro ⟨K, hK, hLK⟩
    have hLperp : ptPerp Γ c L = L := by
      rw [hLK]
      exact ptPerp_neighborSet_eq hP hT hK
    have hLsubX : L ⊆ X := by
      rw [← hLperp]
      exact hLX
    exact hpX (hLsubX hpL)
  have hLhyp : IsHypLine Γ c L :=
    isHypLine_of_isStarLine_not_ordinary hP hT c hL hLnot
  have hLperpHyp : IsHypLine Γ c (ptPerp Γ c L) :=
    isHypLine_ptPerp hP hT c hdeg hreg hLhyp
  have hLperp_card : (ptPerp Γ c L).ncard = t + 1 :=
    IsHypLine.ncard hP hT c hdeg hreg hLperpHyp
  have hMcard : M.ncard = t + 1 :=
    IsHypLine.ncard hP hT c hdeg hreg hMhyp
  have hsub : ptPerp Γ c L ⊆ M := by
    intro z hz
    refine ⟨?_, hLX hz⟩
    rw [mem_ptPerp]
    refine ⟨(mem_ptPerp.mp hz).1, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (mem_ptPerp.mp hz).2 p hpL
  have hEq : ptPerp Γ c L = M :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hLperp_card, hMcard])
  have hdouble := (ptPerp_ptPerp_starLine hP hT c hdeg hreg hL).2
  calc
    L = ptPerp Γ c (ptPerp Γ c L) := hdouble.symm
    _ = ptPerp Γ c M := by rw [hEq]
    _ = conjLine Γ c X p := rfl

theorem disjoint_of_ptPerp_subset (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X L : Set V}
    (hX : IsNonabsPlane Γ c X) (hL : IsStarLine Γ c L) (hLX : ptPerp Γ c L ⊆ X) :
    Disjoint L X := by
  classical
  rw [Set.disjoint_left]
  intro z hzL hzX
  have hLnot : ¬ ∃ K, c K = 1 ∧ L = Γ.neighborSet K := by
    rintro ⟨K, hK, hLK⟩
    have hLperp : ptPerp Γ c L = L := by
      rw [hLK]
      exact ptPerp_neighborSet_eq hP hT hK
    have hsub : Γ.neighborSet K ⊆ X := by
      rw [← hLK, ← hLperp]
      exact hLX
    have h1 := hX.2.2 K hK
    rw [Set.inter_eq_left.mpr hsub] at h1
    have hNcard : (Γ.neighborSet K).ncard = s + 1 := by
      rw [SimpleGraph.ncard_neighborSet, hdeg K, if_neg (by rw [hK]; decide)]
    have hs : 2 ≤ s := two_le_s hP hT c hdeg
    omega
  have hLhyp : IsHypLine Γ c L :=
    isHypLine_of_isStarLine_not_ordinary hP hT c hL hLnot
  obtain ⟨x, y, hx, hxy4, rfl⟩ := hLhyp
  have hzspan : z ∈ spanSet Γ x y := by
    rw [← starLine_eq_spanSet hP hT c hx hxy4]
    exact hzL
  have hz_not : z ∉ ptPerp Γ c (starLine Γ c x y) := by
    rw [ptPerp_starLine_eq_traceSet hP hT c hx hxy4]
    exact fun hzt => (Set.disjoint_left.mp (spanSet_disjoint_traceSet hP hT hxy4)) hzspan hzt
  have hLperpHyp : IsHypLine Γ c (ptPerp Γ c (starLine Γ c x y)) :=
    isHypLine_ptPerp hP hT c hdeg hreg ⟨x, y, hx, hxy4, rfl⟩
  have hLperp_card : (ptPerp Γ c (starLine Γ c x y)).ncard = t + 1 :=
    IsHypLine.ncard hP hT c hdeg hreg hLperpHyp
  have ht : 2 ≤ t := two_le_t hP hT c hdeg
  have h2 : 1 < (ptPerp Γ c (starLine Γ c x y)).ncard := by
    rw [hLperp_card]
    omega
  obtain ⟨w, hw, hwz⟩ := Set.exists_ne_of_one_lt_ncard h2 z
  have hwX : w ∈ X := hLX hw
  have hzw4 : Γ.dist z w = 4 :=
    dist_eq_four_of_mem_of_isOvoid hP hT hX.2 hzX hwX hwz.symm
  have hzw_le : Γ.dist z w ≤ 2 := by
    have h := (mem_ptPerp.mp hw).2 z hzL
    rwa [SimpleGraph.dist_comm] at h
  omega

theorem isConjPlane_comm (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X Y : Set V} :
    IsConjPlane Γ c X Y ↔ IsConjPlane Γ c Y X := by
  constructor
  · rintro ⟨L, hL, hLX, hLY⟩
    obtain ⟨hLperpStar, hLperpEq⟩ := ptPerp_ptPerp_starLine hP hT c hdeg hreg hL
    refine ⟨ptPerp Γ c L, hLperpStar, hLY, ?_⟩
    rw [hLperpEq]
    exact hLX
  · rintro ⟨L, hL, hLY, hLX⟩
    obtain ⟨hLperpStar, hLperpEq⟩ := ptPerp_ptPerp_starLine hP hT c hdeg hreg hL
    refine ⟨ptPerp Γ c L, hLperpStar, hLX, ?_⟩
    rw [hLperpEq]
    exact hLY

theorem isConjPlane_self_iff (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X) :
    IsConjPlane Γ c X X ↔ IsAbsPlane Γ c X := by
  constructor
  · intro hc
    by_contra habs
    have hnon : IsNonabsPlane Γ c X := by
      rcases isStarPlane_cases hP hT c hdeg hreg hX with h | h
      · exact absurd h habs
      · exact h
    obtain ⟨L, hL, hLX, hLXperp⟩ := hc
    have hdisj := disjoint_of_ptPerp_subset hP hT c hdeg hreg hnon hL hLXperp
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hL
    have hxL : x ∈ starLine Γ c x y := mem_starLine_left hx
    exact (Set.disjoint_left.mp hdisj) hxL (hLX hxL)
  · intro habs
    obtain ⟨u, hu, rfl⟩ := habs
    obtain ⟨K, huK⟩ := exists_adj_of_color_zero hT hu
    have hK : c K = 1 := color_eq_one_of_adj_of_color_eq_zero hu huK
    have hKstar : IsStarLine Γ c (Γ.neighborSet K) := isStarLine_neighborSet hP hT hK
    have hsub : Γ.neighborSet K ⊆ ptPerp Γ c {u} := neighborSet_subset_ptPerp hP hK huK
    refine ⟨Γ.neighborSet K, hKstar, hsub, ?_⟩
    rw [ptPerp_neighborSet_eq hP hT hK]
    exact hsub

theorem conjNet_ptPerp (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {u : V} (hu : c u = 0) :
    conjNet Γ c (ptPerp Γ c {u}) = {Y | IsStarPlane Γ c Y ∧ u ∈ Y} := by
  classical
  ext Y
  constructor
  · rintro ⟨hY, L, hL, hLsub, hLY⟩
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hL
    have hxL : x ∈ starLine Γ c x y := mem_starLine_left hx
    have hxP : x ∈ ptPerp Γ c {u} := hLsub hxL
    have hux_le : Γ.dist u x ≤ 2 := by
      have h := (mem_ptPerp.mp hxP).2 u (Set.mem_singleton u)
      rwa [SimpleGraph.dist_comm] at h
    have huL : u ∈ ptPerp Γ c (starLine Γ c x y) := by
      rw [mem_ptPerp]
      refine ⟨hu, ?_⟩
      intro z hz
      have hzP : z ∈ ptPerp Γ c {u} := hLsub hz
      rw [SimpleGraph.dist_comm]
      exact (mem_ptPerp.mp hzP).2 u (Set.mem_singleton u)
    exact ⟨hY, hLY huL⟩
  · rintro ⟨hY, huY⟩
    refine ⟨hY, ?_⟩
    rcases isStarPlane_cases hP hT c hdeg hreg hY with habs | hnon
    · obtain ⟨v, hv, rfl⟩ := habs
      have hdist_le : Γ.dist u v ≤ 2 := (mem_ptPerp.mp huY).2 v (Set.mem_singleton v)
      by_cases huv : u = v
      · subst huv
        obtain ⟨K, huK⟩ := exists_adj_of_color_zero hT hu
        have hK : c K = 1 := color_eq_one_of_adj_of_color_eq_zero hu huK
        have hKstar : IsStarLine Γ c (Γ.neighborSet K) := isStarLine_neighborSet hP hT hK
        have hsub : Γ.neighborSet K ⊆ ptPerp Γ c {u} :=
          neighborSet_subset_ptPerp hP hK huK
        refine ⟨Γ.neighborSet K, hKstar, hsub, ?_⟩
        rw [ptPerp_neighborSet_eq hP hT hK]
        exact hsub
      · have hdist : Γ.dist u v = 2 :=
          dist_eq_two_of_le_two_of_ne hP hu hv huv hdist_le
        let K : V := commonNeighbor hP hdist
        have hK : c K = 1 :=
          color_eq_one_of_adj_of_color_eq_zero hu (commonNeighbor_adj_left hP hdist)
        have hKstar : IsStarLine Γ c (Γ.neighborSet K) := isStarLine_neighborSet hP hT hK
        have hsubU : Γ.neighborSet K ⊆ ptPerp Γ c {u} :=
          neighborSet_subset_ptPerp hP hK (commonNeighbor_adj_left hP hdist)
        have hsubV : Γ.neighborSet K ⊆ ptPerp Γ c {v} :=
          neighborSet_subset_ptPerp hP hK (commonNeighbor_adj_right hP hdist)
        refine ⟨Γ.neighborSet K, hKstar, hsubU, ?_⟩
        rw [ptPerp_neighborSet_eq hP hT hK]
        exact hsubV
    · have hne : Y ≠ ptPerp Γ c {u} := ne_ptPerp_of_isNonabsPlane hP hT c hdeg hnon huY
      have hcount := ncard_hypLines_through_subset hP hT c hdeg hreg hnon.1 huY hne
      have hs : 2 ≤ s := two_le_s hP hT c hdeg
      have hpos : 0 < {l | IsHypLine Γ c l ∧ u ∈ l ∧ l ⊆ Y}.ncard := by
        rw [hcount]
        omega
      obtain ⟨M, hM⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
      obtain ⟨hMhyp, huM, hMY⟩ := hM
      have hMstar : IsStarLine Γ c M := IsHypLine.isStarLine hP hMhyp
      obtain ⟨hLstar, hLEq⟩ := ptPerp_ptPerp_starLine hP hT c hdeg hreg hMstar
      refine ⟨ptPerp Γ c M, hLstar, ?_, ?_⟩
      · intro z hz
        rw [mem_ptPerp]
        refine ⟨(mem_ptPerp.mp hz).1, ?_⟩
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact (mem_ptPerp.mp hz).2 u huM
      · rw [hLEq]
        exact hMY

theorem ptPerp_mem_conjNet_iff (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) {X : Set V} (hX : IsStarPlane Γ c X)
    {u : V} (hu : c u = 0) : ptPerp Γ c {u} ∈ conjNet Γ c X ↔ u ∈ X := by
  classical
  constructor
  · rintro ⟨-, L, hL, hLsub, hLperpSub⟩
    have hu_perp : u ∈ ptPerp Γ c (ptPerp Γ c L) := by
      rw [mem_ptPerp]
      refine ⟨hu, ?_⟩
      intro z hz
      have hzP : z ∈ ptPerp Γ c {u} := hLperpSub hz
      rw [SimpleGraph.dist_comm]
      exact (mem_ptPerp.mp hzP).2 u (Set.mem_singleton u)
    rw [(ptPerp_ptPerp_starLine hP hT c hdeg hreg hL).2] at hu_perp
    exact hLsub hu_perp
  · intro huX
    have hXu : 1 < X.ncard := one_lt_ncard_of_isStarPlane hP hT c hdeg hreg hX
    obtain ⟨v, hvX, hvu⟩ := Set.exists_ne_of_one_lt_ncard hXu u
    have hv : c v = 0 := hX.1.1.1 v hvX
    refine ⟨isStarPlane_ptPerp_singleton hP hT c hdeg hu, ?_⟩
    have hLstar : IsStarLine Γ c (starLine Γ c u v) := isStarLine_starLine hu hv hvu.symm
    refine ⟨starLine Γ c u v, hLstar, ?_, ?_⟩
    · exact hX.1.1.2 u huX v hvX hvu.symm
    · intro z hz
      rw [mem_ptPerp]
      refine ⟨(mem_ptPerp.mp hz).1, ?_⟩
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact (mem_ptPerp.mp hz).2 u (mem_starLine_left hu)

theorem subset_of_isConjPlane (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hii : TalliniCond Γ c) {X Y : Set V}
    (hX : IsStarPlane Γ c X) (hY : IsStarPlane Γ c Y) (hc : IsConjPlane Γ c X Y)
    {p : V} (hpY : p ∈ Y) (hpX : p ∉ X) : conjLine Γ c X p ⊆ Y := by
  classical
  obtain ⟨L, hL, hLX, hLY⟩ := hc
  have hp : c p = 0 := hY.1.1.1 p hpY
  let M : Set V := ptPerp Γ c {p} ∩ X
  have hMstar : IsStarLine Γ c M :=
    isStarLine_inter_ptPerp_singleton_of_isStarPlane hP hT c hdeg hreg hX hp hpX
  have hMcard : M.ncard = t + 1 :=
    ncard_inter_ptPerp_singleton_of_isStarPlane hP hT c hdeg hreg hX hp hpX
  have hNhyp : IsHypLine Γ c (conjLine Γ c X p) :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).1
  have hNp : p ∈ conjLine Γ c X p :=
    (isHypLine_conjLine hP hT c hdeg hreg hX hp hpX).2.1
  have hNperp : ptPerp Γ c (conjLine Γ c X p) = M := by
    change ptPerp Γ c (ptPerp Γ c M) = M
    exact (ptPerp_ptPerp_starLine hP hT c hdeg hreg hMstar).2
  have hMsubX : M ⊆ X := Set.inter_subset_right
  have hLunion : L ∪ M ⊆ X := by
    intro z hz
    rcases hz with hz | hz
    · exact hLX hz
    · exact hMsubX hz
  obtain ⟨V, hVproper, hVsub⟩ := hii L M hL hMstar ⟨X, hX.1, hLunion⟩
  by_cases hNL : ptPerp Γ c L = conjLine Γ c X p
  · intro z hz
    rw [← hNL] at hz
    exact hLY hz
  · have hp_not : p ∉ ptPerp Γ c L := by
      intro hpL
      refine hNL ?_
      have hLperpStar : IsStarLine Γ c (ptPerp Γ c L) :=
        (ptPerp_ptPerp_starLine hP hT c hdeg hreg hL).1
      have hLX' : ptPerp Γ c (ptPerp Γ c L) ⊆ X := by
        rw [(ptPerp_ptPerp_starLine hP hT c hdeg hreg hL).2]
        exact hLX
      exact eq_conjLine hP hT c hdeg hreg hX hpX hLperpStar hpL hLX'
    have hLperpStar : IsStarLine Γ c (ptPerp Γ c L) :=
      (ptPerp_ptPerp_starLine hP hT c hdeg hreg hL).1
    obtain ⟨a, b, ha0, hb0, hab, hLperpEq⟩ := hLperpStar
    have haV : a ∈ V := by
      apply hVsub
      left
      rw [hLperpEq]
      exact mem_starLine_left ha0
    have hbV : b ∈ V := by
      apply hVsub
      left
      rw [hLperpEq]
      exact mem_starLine_right hb0
    have hpV : p ∈ V := by
      apply hVsub
      right
      change p ∈ ptPerp Γ c M
      exact hNp
    have hpab : ¬ IsStarCollinear Γ c p a b := by
      rintro ⟨S, hS, hpS, haS, hbS⟩
      have hS_eq : S = starLine Γ c a b :=
        starLine_eq_of_isStarLine_of_mem hP hT hS haS hbS hab
      have hpa : p ∈ starLine Γ c a b := by
        rw [← hS_eq]
        exact hpS
      exact hp_not (by rw [hLperpEq]; exact hpa)
    have hVplane : IsStarPlane Γ c V :=
      ⟨hVproper, p, hpV, a, haV, b, hbV, hpab⟩
    have haY : a ∈ Y := by
      apply hLY
      rw [hLperpEq]
      exact mem_starLine_left ha0
    have hbY : b ∈ Y := by
      apply hLY
      rw [hLperpEq]
      exact mem_starLine_right hb0
    have hVY : V = Y :=
      eq_of_isStarPlane hP hT c hdeg hreg hVplane hY ⟨hpV, hpY⟩ ⟨haV, haY⟩
        ⟨hbV, hbY⟩ hpab
    intro z hz
    have hzV : z ∈ V := by
      apply hVsub
      right
      change z ∈ ptPerp Γ c M
      exact hz
    rwa [hVY] at hzV

end ConjugacyD

end CFSG.Geometry.GeneralizedQuadrangles
