module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Local

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A : Submodule K W}

theorem perpSpan_sup_eq_ambient_of_dist_eq_four (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p q : V}
    (hp : c p = 0) (hpq : Γ.dist p q = 4) : perpSpan c ι p ⊔ ι q = A := by
  classical
  obtain ⟨s, t, _hs, _ht, _hst, hdeg⟩ := hP.exists_order (by norm_num) hT c
  have hq0 : c q = 0 := by
    have heven : Even (Γ.dist p q) := ⟨2, by rw [hpq]⟩
    have hc := (hP.eq_iff_even_dist c p q).2 heven
    rw [hp] at hc
    exact hc.symm
  have hqne : q ≠ p := by
    intro h
    rw [h] at hpq
    simp at hpq
  let S : Submodule K W := perpSpan c ι p ⊔ ι q
  have hperpS : perpSpan c ι p ≤ S := le_sup_left
  have hqS : ι q ≤ S := le_sup_right
  have hSA : S ≤ A := sup_le (perpSpan_le_ambient hι p) (hι.le_ambient q)
  have hpX : p ∈ sectionPoints c ι S := by
    refine ⟨hp, ?_⟩
    exact (submodule_le_perpSpan (p := p) (x := p) ⟨hp, by simp⟩).trans hperpS
  have hpdeg3 : 3 ≤ (Γ.neighborSet p).ncard := by
    rw [ncard_neighborSet]
    exact hT p
  obtain ⟨L1, hL1p, L2, hL2p, hL12⟩ :=
    (Set.one_lt_ncard (s := Γ.neighborSet p)).mp (by omega)
  have hL1c : c L1 = 1 := color_eq_one_of_adj_of_color_eq_zero hp hL1p
  have hL2c : c L2 = 1 := color_eq_one_of_adj_of_color_eq_zero hp hL2p
  have hline_sec : ∀ L, Γ.Adj p L → Γ.neighborSet L ⊆ sectionPoints c ι S := by
    intro L hpL x hx
    have hLc : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hLc hx
    have hdist : Γ.dist x p ≤ 2 := by
      have h1 : Γ.dist x p ≤ Γ.dist x L + Γ.dist L p := hP.connected.dist_triangle
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hx.symm,
        SimpleGraph.dist_eq_one_iff_adj.mpr hpL.symm] at h1
      omega
    exact ⟨hx0, (submodule_le_perpSpan ⟨hx0, by simpa using hdist⟩).trans hperpS⟩
  have hL1S : ι L1 ≤ S := le_of_neighborSet_subset_sectionPoints hι hL1c (hline_sec L1 hL1p)
  have hL2S : ι L2 ≤ S := le_of_neighborSet_subset_sectionPoints hι hL2c (hline_sec L2 hL2p)
  have hnotnoncol : ¬ IsPairwiseNoncollinear Γ (sectionPoints c ι S) := by
    intro hnc
    have h3 : 3 ≤ (Γ.neighborSet L1).ncard := by
      rw [ncard_neighborSet]
      exact hT L1
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Set.one_lt_ncard (s := Γ.neighborSet L1)).mp (by omega)
    have hxX : x ∈ sectionPoints c ι S := hline_sec L1 hL1p hx
    have hyX : y ∈ sectionPoints c ι S := hline_sec L1 hL1p hy
    have hdist : Γ.dist x y = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hx.symm hy hxy
    exact hnc x hxX y hyX hxy hdist
  have hnotpencil : ¬ IsPencilSection c ι S := by
    rintro ⟨z, _hz0, hzlines, hzpts⟩
    by_cases hzp : z = p
    · have hzlines' : ∀ L, c L = 1 → ι L ≤ S → Γ.Adj p L := by
        intro L h1 h2
        simpa [hzp] using hzlines L h1 h2
      obtain ⟨L, hLc, hLS, hqL⟩ := hzpts q hq0 hqS
      have hpL : Γ.Adj p L := hzlines' L hLc hLS
      have hpq2 : Γ.dist p q = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hpL hqL.symm (Ne.symm hqne)
      omega
    · have hzL1 : Γ.Adj z L1 := hzlines L1 hL1c hL1S
      have hzL2 : Γ.Adj z L2 := hzlines L2 hL2c hL2S
      have hL1eq : L1 = L2 :=
        eq_of_two_common_points hP (Ne.symm hzp) hL1p.symm hzL1.symm hL2p.symm hzL2.symm
      exact hL12 hL1eq
  have htri := section_trichotomy hP hT c hdeg hι hSA
  have hF_exists : ∃ t', 1 ≤ t' ∧ IsFullSubquadrangle c (sectionPoints c ι S) t' := by
    rcases htri with hpencil | hnoncol | hfull
    · exact absurd hpencil hnotpencil
    · exact absurd hnoncol hnotnoncol
    · exact hfull
  obtain ⟨t', ht', hF⟩ := hF_exists
  have hfullp : {L | Γ.Adj p L ∧ Γ.neighborSet L ⊆ sectionPoints c ι S}.ncard = t' + 1 :=
    hF.2.2.1 p hpX
  have hseteq : {L | Γ.Adj p L ∧ Γ.neighborSet L ⊆ sectionPoints c ι S} =
      Γ.neighborSet p := by
    ext L
    constructor
    · rintro ⟨hpL, _⟩
      exact hpL
    · intro hL
      exact ⟨hL, hline_sec L hL⟩
  have hdegp : (Γ.neighborSet p).ncard = t + 1 := by
    rw [ncard_neighborSet, hdeg p, if_pos hp]
  have ht'eq : t' = t := by
    rw [hseteq, hdegp] at hfullp
    omega
  have hXcard : (sectionPoints c ι S).ncard = (s + 1) * (s * t + 1) := by
    rw [ncard_of_isFullSubquadrangle hP hT c hdeg hF, ht'eq]
  have hPcard : (pointFinset c).card = (s + 1) * (s * t + 1) :=
    card_pointFinset hP hT c hdeg
  have hPcardSet : ((pointFinset c : Set V)).ncard = (s + 1) * (s * t + 1) := by
    rw [Set.ncard_coe_finset]
    exact hPcard
  have hXsub : sectionPoints c ι S ⊆ (pointFinset c : Set V) := by
    intro x hx
    simpa using hx.1
  have hXeq : sectionPoints c ι S = (pointFinset c : Set V) :=
    Set.eq_of_subset_of_ncard_le hXsub (by rw [hXcard, hPcardSet])
  have hAleS : A ≤ S := by
    rw [← hι.span]
    refine iSup_le fun x => iSup_le fun hx0 => ?_
    have hxX : x ∈ sectionPoints c ι S := by
      rw [hXeq]
      simpa using hx0
    exact hxX.2
  have hSeqA : S = A := le_antisymm hSA hAleS
  simpa [S] using hSeqA

theorem finrank_perpSpan_add_one (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0) :
    finrank K (perpSpan c ι p) + 1 = finrank K A := by
  classical
  have hpdeg : 0 < Γ.degree p := by
    have := hT p
    omega
  obtain ⟨L, hpL⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := p)).mp hpdeg
  obtain ⟨q, hpq4, -⟩ := hP.exists_dist_eq hT hpL 4 (by norm_num) (by norm_num)
  have hq0 : c q = 0 := by
    have heven : Even (Γ.dist p q) := ⟨2, by rw [hpq4]⟩
    have hc := (hP.eq_iff_even_dist c p q).2 heven
    rw [hp] at hc
    exact hc.symm
  have hqne : q ≠ p := by
    intro h
    rw [h] at hpq4
    simp at hpq4
  have hqnot : ¬ ι q ≤ perpSpan c ι p := by
    intro hle
    have h2 := dist_eq_two_of_le_perpSpan hP hT hι hp hq0 hle hqne
    omega
  have hseq : perpSpan c ι p ⊔ ι q = A :=
    perpSpan_sup_eq_ambient_of_dist_eq_four hP hT hι hp hpq4
  have hq1 : finrank K (ι q) = 1 := hι.finrank_point q hq0
  haveI : FiniteDimensional K (ι q) := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K (perpSpan c ι p) :=
    Submodule.finiteDimensional_of_le (perpSpan_le_ambient hι p)
  have hdisj : perpSpan c ι p ⊓ ι q = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hvspan : ι q = K ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hq1 hv.2 hv0
    have hle : ι q ≤ perpSpan c ι p := by
      rw [hvspan]
      exact (Submodule.span_singleton_le_iff_mem v (perpSpan c ι p)).mpr hv.1
    exact hqnot hle
  have h := Submodule.finrank_sup_add_finrank_inf_eq (perpSpan c ι p) (ι q)
  rw [hdisj, finrank_bot, hq1] at h
  rw [hseq] at h
  omega

theorem perpSpan_sup_eq_of_not_le (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0)
    {X : Submodule K W} (hXA : X ≤ A) (hX : ¬ X ≤ perpSpan c ι p) :
    perpSpan c ι p ⊔ X = A := by
  have hHA : perpSpan c ι p ≤ A := perpSpan_le_ambient hι p
  have hle : perpSpan c ι p ⊔ X ≤ A := sup_le hHA hXA
  haveI : FiniteDimensional K ↥(perpSpan c ι p ⊔ X) := Submodule.finiteDimensional_of_le hle
  have hne : perpSpan c ι p ⊔ X ≠ perpSpan c ι p := by
    intro h
    exact hX (h ▸ le_sup_right)
  have hlt : perpSpan c ι p < perpSpan c ι p ⊔ X :=
    lt_of_le_of_ne le_sup_left (Ne.symm hne)
  have hrank_lt : finrank K (perpSpan c ι p) < finrank K ↥(perpSpan c ι p ⊔ X) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hrank_le : finrank K ↥(perpSpan c ι p ⊔ X) ≤ finrank K A := Submodule.finrank_mono hle
  have hH := finrank_perpSpan_add_one hP hT hι hp
  have hrank : finrank K ↥(perpSpan c ι p ⊔ X) = finrank K A := by omega
  exact Submodule.eq_of_le_of_finrank_eq hle hrank

theorem IsLocalAt.tangent_sup_line (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0)
    {T : Submodule K W} (hTA : T ≤ A) (hT2 : finrank K T = 2) (hpT : ι p ≤ T)
    (hsecond : ∀ x, c x = 0 → ι x ≤ T → ι x = ι p) {L : V} (hpL : Γ.Adj p L) :
    IsLocalAt c ι p (T ⊔ ι L) := by
  classical
  have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
  have hpLle : ι p ≤ ι L := (hι.adj_iff p L hp hL1).1 hpL
  have hL2 : finrank K (ι L) = 2 := hι.finrank_line L hL1
  have hp1 : finrank K (ι p) = 1 := hι.finrank_point p hp
  have hσA : T ⊔ ι L ≤ A := sup_le hTA (hι.le_ambient L)
  haveI : FiniteDimensional K ↥(T ⊔ ι L) := Submodule.finiteDimensional_of_le hσA
  haveI : FiniteDimensional K T := Submodule.finiteDimensional_of_le hTA
  haveI : FiniteDimensional K (ι L) := Submodule.finiteDimensional_of_le (hι.le_ambient L)
  have hpI : ι p ≤ T ⊓ ι L := le_inf hpT hpLle
  have hne : T ≠ ι L := by
    intro hTeq
    have h3 : 3 ≤ (Γ.neighborSet L).ncard := by
      rw [ncard_neighborSet]
      exact hT L
    obtain ⟨y1, hy1, y2, hy2, hy12⟩ :=
      (Set.one_lt_ncard (s := Γ.neighborSet L)).mp (by omega)
    have hy : y1 ≠ p ∨ y2 ≠ p := by
      rcases eq_or_ne y1 p with h1 | h1
      · exact Or.inr fun h2 => hy12 (h1.trans h2.symm)
      · exact Or.inl h1
    rcases hy with hy | hy
    · have hy0 : c y1 = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hy1
      have hyle : ι y1 ≤ T := by
        rw [hTeq]
        exact (hι.adj_iff y1 L hy0 hL1).1 hy1.symm
      exact hy (hι.injective (hsecond y1 hy0 hyle))
    · have hy0 : c y2 = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hy2
      have hyle : ι y2 ≤ T := by
        rw [hTeq]
        exact (hι.adj_iff y2 L hy0 hL1).1 hy2.symm
      exact hy (hι.injective (hsecond y2 hy0 hyle))
  have hlt : T ⊓ ι L < T := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    have hTL : T ≤ ι L := hEq ▸ inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hTL (by rw [hT2, hL2]))
  have hrank_lt : finrank K ↥(T ⊓ ι L) < finrank K T :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hrank_ge : finrank K (ι p) ≤ finrank K ↥(T ⊓ ι L) := Submodule.finrank_mono hpI
  have hinf1 : finrank K ↥(T ⊓ ι L) = 1 := by omega
  have hinf : T ⊓ ι L = ι p :=
    (Submodule.eq_of_le_of_finrank_eq hpI (by rw [hp1, hinf1])).symm
  have hdim : finrank K ↥(T ⊔ ι L) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq T (ι L)
    rw [hinf, hp1, hT2, hL2] at h
    omega
  refine ⟨hpT.trans le_sup_left, ?_⟩
  intro z hz
  by_contra hznot
  have hdist : ¬ Γ.dist z p ≤ 2 := by
    intro hle
    exact hznot ⟨hz.1, by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hle⟩
  have hzp : z ≠ p := by
    rintro rfl
    exact hdist (by simp)
  have hnotzL : ¬ Γ.Adj z L := fun hzL =>
    hdist ((mem_ptPerp_of_adj_of_adj hz.1 hpL hzL).2 p rfl)
  obtain ⟨y, ⟨hLy, hzy⟩, -⟩ := existsUnique_proj_of_not_adj hP hz.1 hL1 hnotzL
  have hy0 : c y = 0 := color_eq_zero_of_dist_eq_two hP hz.1 hzy
  have hyp : y ≠ p := by
    intro h
    rw [h] at hzy
    exact hdist hzy.le
  have hzyne : z ≠ y := by
    rintro rfl
    simp at hzy
  let M := commonNeighbor hP hzy
  have hzM : Γ.Adj z M := commonNeighbor_adj_left hP hzy
  have hyM : Γ.Adj y M := commonNeighbor_adj_right hP hzy
  have hM1 : c M = 1 := color_eq_one_of_adj_of_color_eq_zero hz.1 hzM
  have hM2 : finrank K (ι M) = 2 := hι.finrank_line M hM1
  have hMeq : ι M = ι z ⊔ ι y :=
    line_eq_sup_of_two_adjacent_points hι hz.1 hy0 hzyne hzM hyM
  have hMle : ι M ≤ T ⊔ ι L := by
    rw [hMeq]
    exact sup_le hz.2 (((hι.adj_iff y L hy0 hL1).1 hLy.symm).trans le_sup_right)
  have hpM : ¬ Γ.Adj p M := by
    intro hpM'
    have hML : M = L := eq_of_two_common_points hP (Ne.symm hyp) hpM'.symm hyM.symm hpL.symm hLy
    exact hnotzL (hML ▸ hzM)
  have hlt2 : finrank K ↥(T ⊔ ι L) < finrank K (ι M) + finrank K T := by
    rw [hdim, hM2, hT2]
    omega
  obtain ⟨P, hP1, hPle⟩ :=
    exists_finrank_eq_one_le_inf (X := ι M) (Y := T) (Z := T ⊔ ι L) hMle le_sup_left hlt2
  have hPne : P ≠ ⊥ := by
    intro hPbot
    rw [hPbot, finrank_bot] at hP1
    omega
  have hinfne : ι M ⊓ T ≠ ⊥ := by
    intro hbot
    exact hPne (le_antisymm (hbot ▸ hPle) bot_le)
  obtain ⟨x, hMx, hxT⟩ := exists_adj_le_of_line_inf_ne_bot hι hM1 hinfne
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hM1 hMx
  have hxp : x = p := hι.injective (hsecond x hx0 hxT)
  exact hpM (hxp ▸ hMx.symm)

theorem le_perpSpan_of_isTangentLine (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0)
    {T : Submodule K W} (hTA : T ≤ A) (hTt : IsTangentLine c ι p T) :
    T ≤ perpSpan c ι p := by
  classical
  obtain ⟨hT2, hpT, hkind | hsecond⟩ := hTt
  · obtain ⟨L, hL1, hpL, hLeq⟩ := hkind
    have hLH : ι L ≤ perpSpan c ι p := by
      refine le_of_neighborSet_subset_sectionPoints hι hL1 ?_
      intro x hx
      have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hx
      exact ⟨hx0, submodule_le_perpSpan (mem_ptPerp_of_adj_of_adj hx0 hpL hx.symm)⟩
    rwa [← hLeq]
  · by_contra hnotle
    have hpdeg : 0 < Γ.degree p := by
      have := hT p
      omega
    obtain ⟨L, hpL⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := p)).mp hpdeg
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hp hpL
    have hLH : ι L ≤ perpSpan c ι p := by
      refine le_of_neighborSet_subset_sectionPoints hι hL1 ?_
      intro x hx
      have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL1 hx
      exact ⟨hx0, submodule_le_perpSpan (mem_ptPerp_of_adj_of_adj hx0 hpL hx.symm)⟩
    have hsup : T ⊔ perpSpan c ι p = A := by
      rw [sup_comm]
      exact perpSpan_sup_eq_of_not_le hP hT hι hp hTA hnotle
    have hσloc : IsLocalAt c ι p (T ⊔ ι L) :=
      IsLocalAt.tangent_sup_line hP hT hι hp hTA hT2 hpT hsecond hpL
    have hσA : T ⊔ ι L ≤ A := sup_le hTA (hι.le_ambient L)
    have hA : IsLocalAt c ι p A := by
      have hloc := IsLocalAt.sup_perpSpan hP hT hι hp hσA hσloc
      have hσH : (T ⊔ ι L) ⊔ perpSpan c ι p = A := by
        calc (T ⊔ ι L) ⊔ perpSpan c ι p = T ⊔ (ι L ⊔ perpSpan c ι p) := sup_assoc ..
          _ = T ⊔ perpSpan c ι p := by rw [sup_eq_right.mpr hLH]
          _ = A := hsup
      rwa [hσH] at hloc
    obtain ⟨q, hpq4, -⟩ := hP.exists_dist_eq hT hpL 4 (by norm_num) (by norm_num)
    have hq0 : c q = 0 := by
      have heven : Even (Γ.dist p q) := ⟨2, by rw [hpq4]⟩
      have hc := (hP.eq_iff_even_dist c p q).2 heven
      rw [hp] at hc
      exact hc.symm
    have hmem : q ∈ ptPerp Γ c {p} := hA.2 ⟨hq0, hι.le_ambient q⟩
    have hle2 : Γ.dist q p ≤ 2 := hmem.2 p rfl
    have h4 : Γ.dist q p = 4 := by
      rw [SimpleGraph.dist_comm]
      exact hpq4
    omega

theorem isTangentLine_iff_le_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0)
    {T : Submodule K W} (hT2 : finrank K T = 2) (hpT : ι p ≤ T) (hTA : T ≤ A) :
    IsTangentLine c ι p T ↔ T ≤ perpSpan c ι p :=
  ⟨fun h => le_perpSpan_of_isTangentLine hP hT hι hp hTA h,
   fun h => tangentLine_of_le_perpSpan hP hT hι hp hT2 hpT h⟩

theorem exists_dist_eq_four_of_not_le_perpSpan (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hι : IsProjGQ c ι A) [FiniteDimensional K A] {p : V} (hp : c p = 0)
    {T : Submodule K W} (hT2 : finrank K T = 2) (hpT : ι p ≤ T) (hTA : T ≤ A)
    (hnotle : ¬ T ≤ perpSpan c ι p) :
    ∃ x, c x = 0 ∧ ι x ≤ T ∧ Γ.dist p x = 4 := by
  classical
  have hnot : ¬ IsTangentLine c ι p T := fun h =>
    hnotle ((isTangentLine_iff_le_perpSpan hP hT hι hp hT2 hpT hTA).1 h)
  have hnotsecond : ¬ ∀ x, c x = 0 → ι x ≤ T → ι x = ι p := by
    intro hsecond
    exact hnot ⟨hT2, hpT, Or.inr hsecond⟩
  have hex : ∃ x, c x = 0 ∧ ι x ≤ T ∧ ι x ≠ ι p := by
    by_contra h
    apply hnotsecond
    intro x hx0 hxT
    by_contra hne
    exact h ⟨x, hx0, hxT, hne⟩
  obtain ⟨x, hx0, hxT, hxne⟩ := hex
  have hxp : x ≠ p := by
    intro h
    exact hxne (by rw [h])
  rcases dist_eq_two_or_four_of_color_zero hP hp hx0 (Ne.symm hxp) with h2 | h4
  · exfalso
    have hTeq : T = ι p ⊔ ι x :=
      submodule_eq_sup_of_finrank_two hT2 (hι.finrank_point p hp) (hι.finrank_point x hx0)
        (fun h => hxp (hι.injective h).symm) hpT hxT
    have hxperp : x ∈ ptPerp Γ c {p} := by
      refine ⟨hx0, ?_⟩
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [SimpleGraph.dist_comm]
      omega
    have hTH : T ≤ perpSpan c ι p := by
      rw [hTeq]
      exact sup_le (submodule_le_perpSpan ⟨hp, by simp⟩) (submodule_le_perpSpan hxperp)
    exact hnotle hTH
  · exact ⟨x, hx0, hxT, h4⟩

end CFSG.Geometry.GeneralizedQuadrangles

end
