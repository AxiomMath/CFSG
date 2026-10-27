module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Setting
public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Closure3

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem degree_subquadrangleGraph (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) (v : subquadrangleSet Γ c P') :
    (Γ.induce (subquadrangleSet Γ c P')).degree v =
      if subquadrangleColoring c P' v = 0 then q + 1 else q ^ 2 + 1 := by
  obtain ⟨x, hxS⟩ := v
  rcases mem_subquadrangleSet.mp hxS with hxP | hxL
  · have hv : (⟨x, hxS⟩ : subquadrangleSet Γ c P') =
        ⟨x, mem_subquadrangleSet.mpr (Or.inl hxP)⟩ := Subtype.ext rfl
    rw [hv, degree_subquadrangleGraph_of_mem_point c hF hxP,
      if_pos (by rw [subquadrangleColoring_apply, hF.1 x hxP])]
  · have hv : (⟨x, hxS⟩ : subquadrangleSet Γ c P') =
        ⟨x, mem_subquadrangleSet.mpr (Or.inr (mem_subquadrangleLines.mp hxL))⟩ :=
      Subtype.ext rfl
    rw [hv, degree_subquadrangleGraph_of_mem_line c hΓ.deg hF hxL,
      if_neg (by rw [subquadrangleColoring_apply, (mem_subquadrangleLines.mp hxL).1]; decide)]

private theorem exists_fullSubquadrangle_of_isThas (hΓ : IsThasQuadrangle Γ c q) {L M : V}
    (hL : c L = 1) (hLM : Γ.dist L M = 4) :
    ∃ P' : Set V, IsFullSubquadrangle c P' q ∧ Γ.neighborSet L ⊆ P' ∧
      Γ.neighborSet M ⊆ P' := by
  have h1 : 1 < q := by have h := hΓ.two_le; omega
  have h2 : q < q ^ 3 := lt_self_pow₀ h1 (by norm_num)
  obtain ⟨P', hLP, hMP, hF⟩ :=
    exists_fullSubquadrangle hΓ.gp hΓ.thick c hΓ.deg hΓ.propH hΓ.span h1 h2 hL hLM
  exact ⟨P', hF, hLP, hMP⟩

private theorem eq_secondParameter_of_fullSubquadrangle_of_subset (hΓ : IsThasQuadrangle Γ c q)
    {P₀ Q : Set V} (hF₀ : IsFullSubquadrangle c P₀ q) (hQsub : Q ⊆ P₀) {t'' : ℕ}
    (hFQ : IsFullSubquadrangle c Q t'') (hQne : Q.Nonempty) (ht'' : 1 ≤ t'') : t'' = q := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hq : 2 ≤ q := hΓ.two_le
  have hS : IsGeneralizedPolygon (Γ.induce (subquadrangleSet Γ c P₀)) 4 :=
    isGeneralizedPolygon_subquadrangleGraph hP hT c hΓ.deg hF₀
  have hTS : IsThick (Γ.induce (subquadrangleSet Γ c P₀)) :=
    isThick_subquadrangleGraph hP hT c hΓ.deg hF₀ hq
  have hdegS : ∀ v : subquadrangleSet Γ c P₀,
      (Γ.induce (subquadrangleSet Γ c P₀)).degree v =
        if subquadrangleColoring c P₀ v = 0 then q + 1 else q ^ 2 + 1 :=
    fun v => degree_subquadrangleGraph hΓ hF₀ v
  have hneS : {v : subquadrangleSet Γ c P₀ | (v : V) ∈ Q}.Nonempty := by
    obtain ⟨x, hx⟩ := hQne
    exact ⟨⟨x, mem_subquadrangleSet.mpr (Or.inl (hQsub hx))⟩, hx⟩
  have hF' : ∀ x ∈ {v : subquadrangleSet Γ c P₀ | (v : V) ∈ Q},
      subquadrangleColoring c P₀ x = 0 := by
    intro x hx
    rw [subquadrangleColoring_apply]
    exact hFQ.1 (x : V) hx
  have hB' : ∀ L ∈ {v : subquadrangleSet Γ c P₀ | (v : V) ∈ subquadrangleLines Γ c Q},
      subquadrangleColoring c P₀ L = 1 := by
    intro L hL
    rw [subquadrangleColoring_apply]
    exact (mem_subquadrangleLines.mp hL).1
  have hBF' : ∀ L ∈ {v : subquadrangleSet Γ c P₀ | (v : V) ∈ subquadrangleLines Γ c Q},
      ∀ x, (Γ.induce (subquadrangleSet Γ c P₀)).Adj L x → (x : V) ∈ Q := by
    intro L hL x hx
    exact (mem_subquadrangleLines.mp hL).2 (SimpleGraph.induce_adj.mp hx)
  have hFB' : ∀ x ∈ {v : subquadrangleSet Γ c P₀ | (v : V) ∈ Q},
      ((Γ.induce (subquadrangleSet Γ c P₀)).neighborSet x ∩
        {v : subquadrangleSet Γ c P₀ | (v : V) ∈ subquadrangleLines Γ c Q}).ncard = t'' + 1 := by
    intro x hx
    have hxQ : (x : V) ∈ Q := hx
    have hcongr : ((Γ.induce (subquadrangleSet Γ c P₀)).neighborSet x ∩
        {v : subquadrangleSet Γ c P₀ | (v : V) ∈ subquadrangleLines Γ c Q}).ncard =
        (fullLinesThrough Γ Q (x : V)).ncard := by
      refine Set.ncard_congr (fun K _ => (K : V)) ?_ ?_ ?_
      · intro K hK
        exact ⟨SimpleGraph.induce_adj.mp hK.1, (mem_subquadrangleLines.mp hK.2).2⟩
      · intro K _ K' _ heq
        exact Subtype.ext heq
      · intro b hb
        obtain ⟨hbx, hbN⟩ := hb
        have hbline : c b = 1 :=
          color_eq_one_of_adj_of_color_eq_zero (hFQ.1 (x : V) hxQ) hbx
        have hbS : b ∈ subquadrangleSet Γ c P₀ :=
          mem_subquadrangleSet.mpr
            (Or.inr (mem_subquadrangleLines.mpr ⟨hbline, fun z hz => hQsub (hbN hz)⟩))
        exact ⟨⟨b, hbS⟩,
          ⟨SimpleGraph.induce_adj.mpr hbx, mem_subquadrangleLines.mpr ⟨hbline, hbN⟩⟩, rfl⟩
    rw [hcongr]
    exact hFQ.2.2.1 (x : V) hxQ
  have hFF' : ∀ x ∈ {v : subquadrangleSet Γ c P₀ | (v : V) ∈ Q},
      ∀ y ∈ {v : subquadrangleSet Γ c P₀ | (v : V) ∈ Q}, x ≠ y →
      ∀ L, (Γ.induce (subquadrangleSet Γ c P₀)).Adj x L →
        (Γ.induce (subquadrangleSet Γ c P₀)).Adj y L →
        L ∈ {v : subquadrangleSet Γ c P₀ | (v : V) ∈ subquadrangleLines Γ c Q} := by
    intro x hx y hy hxy L hxL hyL
    have hxQ : (x : V) ∈ Q := hx
    have hyQ : (y : V) ∈ Q := hy
    have hxyV : (x : V) ≠ (y : V) := fun h => hxy (Subtype.ext h)
    have hxL' : Γ.Adj (x : V) (L : V) := SimpleGraph.induce_adj.mp hxL
    have hyL' : Γ.Adj (y : V) (L : V) := SimpleGraph.induce_adj.mp hyL
    have hline : c (L : V) = 1 :=
      color_eq_one_of_adj_of_color_eq_zero (hFQ.1 (x : V) hxQ) hxL'
    have hNQ : Γ.neighborSet (L : V) ⊆ Q := by
      have h2 : 2 ≤ (Γ.neighborSet (L : V) ∩ Q).ncard := by
        have hsub : ({(x : V), (y : V)} : Set V) ⊆ Γ.neighborSet (L : V) ∩ Q := by
          intro w hw
          rcases hw with hw | hw
          · rw [hw]; exact ⟨hxL'.symm, hxQ⟩
          · rw [hw]; exact ⟨hyL'.symm, hyQ⟩
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_pair hxyV] at hle
        omega
      exact hFQ.2.1 (L : V) hline h2
    exact mem_subquadrangleLines.mpr ⟨hline, hNQ⟩
  have hres := eq_or_mul_le_of_closed_dual (Γ := Γ.induce (subquadrangleSet Γ c P₀))
    hS hTS (subquadrangleColoring c P₀) (s := q ^ 2) (t := q) hdegS
    (F := {v : subquadrangleSet Γ c P₀ | (v : V) ∈ Q})
    (B := {v : subquadrangleSet Γ c P₀ | (v : V) ∈ subquadrangleLines Γ c Q})
    (p := t'') hF' hB' hBF' hFB' hFF' hneS
  rcases hres with h | h
  · exact h
  · exfalso
    have hq1 : 1 < q := by omega
    have hq2 : q < q ^ 2 := lt_self_pow₀ hq1 (by norm_num)
    have hge : q ^ 2 ≤ t'' * q ^ 2 := by
      calc q ^ 2 = 1 * q ^ 2 := (one_mul _).symm
        _ ≤ t'' * q ^ 2 := Nat.mul_le_mul_right _ ht''
    omega

private theorem eq_of_isFullSubquadrangle_of_neighborSet_subset (hΓ : IsThasQuadrangle Γ c q)
    {L M : V} (hL : c L = 1) (hLM : Γ.dist L M = 4) {P₀ P₁ : Set V}
    (hF₀ : IsFullSubquadrangle c P₀ q) (hL₀ : Γ.neighborSet L ⊆ P₀)
    (hM₀ : Γ.neighborSet M ⊆ P₀) (hF₁ : IsFullSubquadrangle c P₁ q)
    (hL₁ : Γ.neighborSet L ⊆ P₁) (hM₁ : Γ.neighborSet M ⊆ P₁) : P₁ = P₀ := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hM : c M = 1 := by
    have hc : c L = c M :=
      (hP.eq_iff_even_dist c L M).2 (by rw [hLM]; exact ⟨2, by norm_num⟩)
    rw [hL] at hc
    exact hc.symm
  have h0Q : ∀ x ∈ P₀ ∩ P₁, c x = 0 := fun x hx => hF₀.1 x hx.1
  have hfullQ : ∀ K, c K = 1 → 2 ≤ (Γ.neighborSet K ∩ (P₀ ∩ P₁)).ncard →
      Γ.neighborSet K ⊆ P₀ ∩ P₁ := by
    intro K hK h2
    have h2₀ : 2 ≤ (Γ.neighborSet K ∩ P₀).ncard :=
      le_trans h2 (Set.ncard_le_ncard (fun z hz => ⟨hz.1, hz.2.1⟩) (Set.toFinite _))
    have h2₁ : 2 ≤ (Γ.neighborSet K ∩ P₁).ncard :=
      le_trans h2 (Set.ncard_le_ncard (fun z hz => ⟨hz.1, hz.2.2⟩) (Set.toFinite _))
    intro z hz
    exact ⟨hF₀.2.1 K hK h2₀ hz, hF₁.2.1 K hK h2₁ hz⟩
  have hLpos : 0 < (Γ.neighborSet L).ncard := by
    rw [SimpleGraph.ncard_neighborSet, hΓ.deg L, if_neg (by rw [hL]; decide)]
    exact Nat.succ_pos _
  obtain ⟨x, hxL⟩ := (Set.ncard_pos (s := Γ.neighborSet L)).mp hLpos
  have hMpos : 1 < (Γ.neighborSet M).ncard := by
    have h2 : 2 ≤ q ^ 2 := by
      calc 2 ≤ q := hΓ.two_le
        _ ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    rw [SimpleGraph.ncard_neighborSet, hΓ.deg M, if_neg (by rw [hM]; decide)]
    omega
  obtain ⟨yx, ⟨hyxM, hxyx2⟩, -⟩ :=
    existsUnique_adj_dist_two_of_mem_neighborSet hP c hL hxL hM hLM
  obtain ⟨y, hyM, hyne⟩ := Set.exists_ne_of_one_lt_ncard hMpos yx
  have hxy4 : Γ.dist x y = 4 :=
    dist_eq_four_of_mem_neighborSet_of_ne_proj hP c hL hxL hM hLM hyM hyxM hxyx2 hyne
  obtain ⟨xy, ⟨hxyL, hxyy⟩, -⟩ :=
    existsUnique_adj_dist_two_of_mem_neighborSet hP c hM hyM hL
      (by rw [SimpleGraph.dist_comm]; exact hLM)
  have hxyx : xy ≠ x := by
    intro h
    rw [h, SimpleGraph.dist_comm] at hxyy
    omega
  have htrace_xy : xy ∈ traceSet Γ x y :=
    ⟨dist_eq_two_of_adj_of_adj_of_ne hP hxL.symm hxyL hxyx.symm, hxyy⟩
  have htrace_yx : yx ∈ traceSet Γ x y :=
    ⟨hxyx2, dist_eq_two_of_adj_of_adj_of_ne hP hyM.symm hyxM hyne⟩
  have hLMne : L ≠ M := by
    intro h
    rw [h, SimpleGraph.dist_self] at hLM
    omega
  have hne_xy_yx : xy ≠ yx := by
    intro h
    have hmem : Γ.Adj L yx := h ▸ hxyL
    have h2 : Γ.dist L M = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hmem hyxM.symm hLMne
    omega
  have hquadQ : ∃ x ∈ P₀ ∩ P₁, ∃ y ∈ P₀ ∩ P₁, Γ.dist x y = 4 ∧
      2 ≤ (traceSet Γ x y ∩ (P₀ ∩ P₁)).ncard := by
    refine ⟨x, ⟨hL₀ hxL, hL₁ hxL⟩, y, ⟨hM₀ hyM, hM₁ hyM⟩, hxy4, ?_⟩
    have hlt : 1 < (traceSet Γ x y ∩ (P₀ ∩ P₁)).ncard :=
      (Set.one_lt_ncard (s := traceSet Γ x y ∩ (P₀ ∩ P₁))).mpr
        ⟨xy, ⟨htrace_xy, hL₀ hxyL, hL₁ hxyL⟩,
          yx, ⟨htrace_yx, hM₀ hyxM, hM₁ hyxM⟩, hne_xy_yx⟩
    omega
  obtain ⟨t'', ht''1, hFQ⟩ := exists_isFullSubquadrangle hP hT c hΓ.deg h0Q hfullQ hquadQ
  have ht''q : t'' = q :=
    eq_secondParameter_of_fullSubquadrangle_of_subset hΓ hF₀ Set.inter_subset_left hFQ
      ⟨x, hL₀ hxL, hL₁ hxL⟩ ht''1
  have hQcard : (P₀ ∩ P₁).ncard = (q ^ 2 + 1) * (q ^ 2 * q + 1) := by
    rw [ncard_of_isFullSubquadrangle hP hT c hΓ.deg hFQ, ht''q]
  have hP₀card : P₀.ncard = (q ^ 2 + 1) * (q ^ 2 * q + 1) :=
    ncard_of_isFullSubquadrangle hP hT c hΓ.deg hF₀
  have hQeq : P₀ ∩ P₁ = P₀ :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hQcard, hP₀card])
  have hP₀P₁ : P₀ ⊆ P₁ := by
    intro z hz
    rw [← hQeq] at hz
    exact hz.2
  have hP₁card : P₁.ncard = (q ^ 2 + 1) * (q ^ 2 * q + 1) :=
    ncard_of_isFullSubquadrangle hP hT c hΓ.deg hF₁
  exact (Set.eq_of_subset_of_ncard_le hP₀P₁ (by rw [hP₀card, hP₁card])).symm

theorem existsUnique_fullSubquadrangle (hΓ : IsThasQuadrangle Γ c q) {L M : V} (hL : c L = 1)
    (hLM : Γ.dist L M = 4) :
    ∃! P' : Set V, IsFullSubquadrangle c P' q ∧ Γ.neighborSet L ⊆ P' ∧
      Γ.neighborSet M ⊆ P' := by
  obtain ⟨P₀, hF₀, hL₀, hM₀⟩ := exists_fullSubquadrangle_of_isThas hΓ hL hLM
  refine ⟨P₀, ⟨hF₀, hL₀, hM₀⟩, ?_⟩
  rintro P₁ ⟨hF₁, hL₁, hM₁⟩
  exact eq_of_isFullSubquadrangle_of_neighborSet_subset hΓ hL hLM hF₀ hL₀ hM₀ hF₁ hL₁ hM₁

private theorem isFullSubquadrangle_spanUnion_of_isThas (hΓ : IsThasQuadrangle Γ c q) {U V : V}
    (hU : c U = 1) (hV : c V = 1) (hUV : Γ.dist U V = 4) :
    IsFullSubquadrangle c (spanUnion hΓ.gp U V) q := by
  have h1 : 1 < q := by have h := hΓ.two_le; omega
  exact isFullSubquadrangle_spanUnion hΓ.gp hΓ.thick c hΓ.deg hΓ.span hU hV hUV
    (lineClosure hΓ.gp hΓ.thick c hΓ.propH hΓ.deg hΓ.span hU hV hUV h1) h1
    (lt_self_pow₀ h1 (by norm_num))

theorem spanSet_subset_of_isFullSubquadrangle (hΓ : IsThasQuadrangle Γ c q) {P' : Set V}
    (hF : IsFullSubquadrangle c P' q) {x y : V} (hx : x ∈ P') (hy : y ∈ P')
    (hxy : Γ.dist x y = 4) : spanSet Γ x y ⊆ P' := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  have hq : 2 ≤ q := hΓ.two_le
  have hxyne : x ≠ y := by
    intro h
    rw [h, SimpleGraph.dist_self] at hxy
    omega
  have hx0 : c x = 0 := hF.1 x hx
  have hy0 : c y = 0 := hF.1 y hy
  have hposx : 0 < (fullLinesThrough Γ P' x).ncard := by
    rw [show fullLinesThrough Γ P' x = {L | Γ.Adj x L ∧ Γ.neighborSet L ⊆ P'} from rfl,
      hF.2.2.1 x hx]
    exact Nat.succ_pos _
  obtain ⟨U, hxU⟩ := (Set.ncard_pos (s := fullLinesThrough Γ P' x)).mp hposx
  have hxUy : Γ.Adj x U := hxU.1
  have hUline : c U = 1 := color_eq_one_of_adj_of_color_eq_zero hx0 hxUy
  have hyU : Γ.dist y U = 3 := by
    have hnot : ¬ Γ.Adj y U := by
      intro hYU
      have h2 : Γ.dist x y = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hxUy hYU.symm hxyne
      omega
    exact dist_eq_three_of_not_adj_of_color_ne hP c hnot (by rw [hy0, hUline]; decide)
  let p : V := proj hP hyU
  have hpU : Γ.Adj U p := proj_adj hP hyU
  have hyp : Γ.dist y p = 2 := proj_dist hP hyU
  have hpP : p ∈ P' := hxU.2 hpU
  have hpy : p ≠ y := by
    intro h
    rw [h] at hyp
    simp at hyp
  let V₀ : V := commonNeighbor hP hyp
  have hV₀y : Γ.Adj y V₀ := commonNeighbor_adj_left hP hyp
  have hV₀p : Γ.Adj p V₀ := commonNeighbor_adj_right hP hyp
  have hposy : 1 < (fullLinesThrough Γ P' y).ncard := by
    rw [show fullLinesThrough Γ P' y = {L | Γ.Adj y L ∧ Γ.neighborSet L ⊆ P'} from rfl,
      hF.2.2.1 y hy]
    omega
  obtain ⟨V, hVy, hVne⟩ := Set.exists_ne_of_one_lt_ncard hposy V₀
  have hVy' : Γ.Adj y V := hVy.1
  have hVline : c V = 1 := color_eq_one_of_adj_of_color_eq_zero hy0 hVy'
  have hUV4 : Γ.dist U V = 4 := by
    have hne : U ≠ V := by
      intro h
      have hxV : Γ.Adj x V := h ▸ hxUy
      have h2 : Γ.dist x y = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hxV hVy'.symm hxyne
      omega
    have hnot2 : Γ.dist U V ≠ 2 := by
      intro h2
      obtain ⟨z, hUz, hzV⟩ :=
        hP.exists_adj_dist_succ (y := V) (v := U) (by rw [SimpleGraph.dist_comm, h2]; norm_num)
      have hVU : Γ.dist V U = 2 := by rw [SimpleGraph.dist_comm]; exact h2
      rw [hVU] at hzV
      have hVz : Γ.Adj V z := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
      have hzyne : y ≠ z := by
        intro h
        have hyU : Γ.Adj y U := h.symm ▸ hUz.symm
        have h2' : Γ.dist x y = 2 :=
          dist_eq_two_of_adj_of_adj_of_ne hP hxUy hyU.symm hxyne
        omega
      have hzy : Γ.dist y z = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hVy' hVz hzyne
      have hzp : z = p :=
        (existsUnique_proj hP hyU).unique ⟨hUz, hzy⟩ ⟨hpU, hyp⟩
      have hVp : Γ.Adj p V := (hzp ▸ hVz).symm
      exact hVne ((existsUnique_commonNeighbor hP hyp).unique ⟨hVy', hVp⟩ ⟨hV₀y, hV₀p⟩)
    have heven : Even (Γ.dist U V) :=
      (hP.eq_iff_even_dist c U V).1 (by rw [hUline, hVline])
    have hle : Γ.dist U V ≤ 4 := hP.dist_le (by norm_num) U V
    have hne0 : Γ.dist U V ≠ 0 := by
      intro h0
      exact hne ((hP.connected.dist_eq_zero_iff).mp h0)
    obtain ⟨k, hk⟩ := heven
    omega
  have hFspan : IsFullSubquadrangle c (spanUnion hP U V) q :=
    isFullSubquadrangle_spanUnion_of_isThas hΓ hUline hVline hUV4
  have hEq : P' = spanUnion hP U V :=
    (existsUnique_fullSubquadrangle hΓ hUline hUV4).unique ⟨hF, hxU.2, hVy.2⟩
      ⟨hFspan, neighborSet_subset_spanUnion_left hP hT c hUline hVline hUV4,
        neighborSet_subset_spanUnion_right hP hT c hUline hVline hUV4⟩
  intro z hz
  rw [← spanOrLine_of_dist_eq_four hP hxy] at hz
  rw [hEq]
  exact spanOrLine_subset_spanUnion hP hxUy.symm hVy'.symm hz

end CFSG.Geometry.GeneralizedQuadrangles
