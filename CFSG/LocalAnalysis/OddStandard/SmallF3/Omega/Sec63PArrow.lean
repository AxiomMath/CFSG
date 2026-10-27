module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PFalse
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Om5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_not_om6p [Finite G] {Y : Subgroup G} (hq : IsQuasisimple ↥Y)
    (h : IsOmega5 Y ∨ IsL281 Y) (h6 : IsOmega6Plus Y) : False := by
  have h3 := ctrQ_of_l43 hq h6
  rcases h with h | h
  · rw [ctrQ_of_psp4 hq h] at h3
    omega
  · rw [ctrQ_of_l281 hq h] at h3
    omega

theorem sec63_arrow_rank_aux' [Finite G] (h33 : Asc82Lemma33) (hF : Asc82AutFacts) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {x y : G}
    {X Y T : Subgroup G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hXc : IsComponentIn X (centralizer ({x} : Set G)))
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hXY : X ≤ Y) (hcomm : ⁅Y, zpowers x⁆ = Y)
    (hXF : InFStar X) (hYF : InFStar Y) (hYC : InCStar Y) (hX29 : IsL29 X)
    (hYs : IsOmega5 Y ∨ IsL281 Y) (hT : IsSylow2Of T (centralizer (X : Set G)))
    (hxT : x ∈ T) (hyT : y ∈ T) : CFSG.Open.pRank 2 T ≤ 2 := by
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hxN : x ∈ normalizer (Y : Set G) := sec63_mem_normalizer_of_comm hcomm
  have hyH : y ∈ centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYc.1 ha)
  have hxH : x ∉ centralizer (Y : Set G) := by
    intro hxc
    have hYx : Y ≤ centralizer ({x} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hxc a ha)
    have hbot := commutator_zpowers_eq_bot_of_le_centralizer hYx
    rw [hcomm] at hbot
    exact hYc.ne_bot hbot
  have hUcyc : IsCyclic ↥(T ⊓ centralizer (Y : Set G)) := sec63_isCyclic_inf h33 hS hYC hYF hT2
  have hUcyc' : IsCyclic ↥(T ⊓ centralizer ({y} : Set G) ⊓ centralizer (Y : Set G)) := by
    haveI : IsCyclic ↥(T ⊓ centralizer (Y : Set G)) := hUcyc
    exact Subgroup.isCyclic_of_le (inf_le_inf inf_le_left le_rfl)
  have hRN : T ⊓ centralizer ({y} : Set G) ≤
      normalizer (Y : Set G) ⊓ centralizer (X : Set G) := by
    intro r hr
    refine ⟨?_, hT.1 hr.1⟩
    refine sec63_mem_normalizer_of_centralizes hYc hr.2 hXc hXY ?_
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hT.1 hr.1) a ha).symm
  rcases sec63_arrow_cases hF hHyp hx hy hxN hXc hYc hXY hXF (Or.inr hYs)
    (hT2.to_le inf_le_left) hRN with hrel | ⟨-, hY6, -⟩
  · exact sec63_caseA hT2 hy hyT hyH hxT hxy hxH hUcyc' hrel
  · exact (sec63P_not_om6p hYc.isQuasisimple hYs hY6).elim

theorem sec63_arrow_rank' [Finite G] (h33 : Asc82Lemma33) (hF : Asc82AutFacts) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {x y : G}
    {X Y : Subgroup G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hXc : IsComponentIn X (centralizer ({x} : Set G)))
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hXY : X ≤ Y) (hcomm : ⁅Y, zpowers x⁆ = Y)
    (hXF : InFStar X) (hYF : InFStar Y) (hYC : InCStar Y) (hX29 : IsL29 X)
    (hYs : IsOmega5 Y ∨ IsL281 Y) :
    ∃ T : Subgroup G, IsSylow2Of T (centralizer (X : Set G)) ∧ CFSG.Open.pRank 2 T ≤ 2 := by
  have hxX : x ∈ centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hXc.1 ha)
  have hyX : y ∈ centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYc.1 (hXY ha))
  obtain ⟨T, hT, hxT, hyT⟩ := sec63_exists_sylow_pair hx hy hxy hxX hyX
  exact ⟨T, hT, sec63_arrow_rank_aux' h33 hF hS hHyp hx hy hxy hXc hYc hXY hcomm hXF hYF hYC
    hX29 hYs hT hxT hyT⟩

theorem asc82Lemma63_of' (h33 : Asc82Lemma33) (h35 : Asc82Lemma35) (h36 : Asc82Lemma36)
    (hsh : Asc82Shapes) (hP : Asc82Tab6P) (hM : Asc82Tab6M) (hF : Asc82AutFacts)
    (hA6 : Asc82FactOm6PA6) : Asc82Lemma63 := by
  intro G _ _ t L hS hHyp x hx X₁ X₂ h1c h1F h2c h2F
  by_contra hne
  have hbad : Bad63 X₁ x := ⟨hx, h1c, h1F, X₂, fun h => hne h.symm, h2c, h2F⟩
  obtain ⟨Y, hch, hYC⟩ := exists_inCStar_of_inC (⟨x, hx, h1c⟩ : InC X₁)
  obtain ⟨V, v, hVbad, hVY⟩ := sec63_last_bad hS.a2 hch ⟨x, hbad⟩
  have hYF : InFStar Y := inFStar_of_walterChain hS.a2 hch h1F
  have hVshape := sec63_bad_shape h36 hS hVbad
  obtain ⟨hv, hVc, hVF, W, hWne, hWc, hWF⟩ := id hVbad
  have hWshape : IsL29 W ∨ IsL281 W :=
    sec63_bad_shape h36 hS (sec63_bad_swap hVbad hWne hWc hWF)
  have hfinish : (∃ T : Subgroup G, IsSylow2Of T (centralizer (V : Set G)) ∧
      CFSG.Open.pRank 2 T ≤ 2) → False := by
    rintro ⟨T, hT, hr⟩
    exact sec63_false_of_rank hv hVc hWc hWne hWshape hT hr
  have hOm6M : ∀ {Y' : Subgroup G} {y' : G}, orderOf y' = 2 →
      IsComponentIn Y' (centralizer ({y'} : Set G)) → InFStar Y' → V ≤ Y' →
      IsOmega6Minus Y' → False :=
    fun hy' hY'c hY'F hVY' hY6 =>
      sec63_not_omega6Minus h35 hM hF hS hv hVc hWc hWF hWne hy' hY'c hY'F hVY' hY6
  rcases sec63_plain_chain hsh hS hVF hVshape hVY with
    hVYeq | ⟨hV29, hVarr, hYsh⟩ | ⟨hV29, Z, hVZ, hZ5, hZY, hYsh⟩
  · subst hVYeq
    obtain ⟨T, hT⟩ : ∃ T : Subgroup G, IsSylow2Of T (centralizer (V : Set G)) :=
      ⟨_, isSylow2Of_map_sylow (Classical.arbitrary (Sylow 2 ↥(centralizer (V : Set G))))⟩
    have hcyc : IsCyclic ↥(T ⊓ centralizer (V : Set G)) :=
      sec63_isCyclic_inf h33 hS hYC hYF hT.2.1
    rw [inf_eq_left.mpr hT.1] at hcyc
    exact hfinish ⟨T, hT, (sec65_pRank_cyclic hcyc).trans (by norm_num)⟩
  · obtain ⟨x', y', hx', hy', hxy', hVc', hYc', hVY', hcomm'⟩ := hVarr
    rcases hYsh with hY | hY | hY | hY
    · exact hfinish (sec63_arrow_rank' h33 hF hS hHyp hx' hy' hxy' hVc' hYc' hVY' hcomm'
        hVF hYF hYC hV29 (Or.inr hY))
    · exact hfinish (sec63_arrow_rank' h33 hF hS hHyp hx' hy' hxy' hVc' hYc' hVY' hcomm'
        hVF hYF hYC hV29 (Or.inl hY))
    · exact (sec63_om6p_false h33 h35 h36 hsh hM hF hA6 hS hHyp hVbad hWc hWF hWne hx' hy' hxy'
        hVc' hYc' hVY' hcomm' hVF hYF hYC hV29 hY).elim
    · exact hOm6M hy' hYc' hYF hVY' hY
  · obtain ⟨-, -, -, -, -, -, -, hVZle, -⟩ := hVZ
    obtain ⟨xZ, yZ, -, hyZ, -, -, hYc'', hZYle, -⟩ := id hZY
    rcases hYsh with hY | hY
    · exact sec63_no_om5_om6p hP hHyp hZY hZ5 hY
    · exact hOm6M hyZ hYc'' hYF (hVZle.trans hZYle) hY

end CFSG.OddStandard.SmallF3.Omega
