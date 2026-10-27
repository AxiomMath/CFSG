module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotStep3Normalize
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotStep3Lift
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)

section Model


theorem iSup_levi_adjDatumE6_eq_top (K : Type) [Field K] :
    ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1 = ⊤ :=
  CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
    (CFSG.LieType.RootSystem.isCTRootSystem (adjDatumE6 K).isFiniteType
      (adjDatumE6 K).divisible) (adjDatum_isCTGroupDatum (rootOperatorFamily .E6) K)

theorem map_subtype_map_fixedFieldInclusion_leviTorus_E6 {K₂ : Type} [Field K₂] (σ : K₂ ≃+* K₂)
    (J : Finset (Fin (Tag.rank .E6))) :
    (((leviTorus (fixSubfield σ) J).subgroupOf (adjointGroup .E6 (fixSubfield σ))).map
        (fixedFieldInclusion σ)).map (adjointGroup .E6 K₂).subtype =
      (leviTorus (fixSubfield σ) J ⊓ adjointGroup .E6 (fixSubfield σ)).map
        (baseChangeGL (fixSubfield σ).subtype) := by
  rw [Subgroup.map_map]
  have h : (adjointGroup .E6 K₂).subtype.comp (fixedFieldInclusion σ) =
      (baseChangeGL (fixSubfield σ).subtype).comp (adjointGroup .E6 (fixSubfield σ)).subtype :=
    MonoidHom.ext fun g => coe_fixedFieldInclusion σ g
  rw [h, ← Subgroup.map_map, subgroupOf_map_subtype]

theorem perfectCore_centralizer_map_fixedFieldInclusion_leviTorus_E6 {K₂ : Type} [Field K₂]
    [Finite K₂] (σ : K₂ ≃+* K₂) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) :
    perfectCore (centralizer ((((leviTorus (fixSubfield σ) J).subgroupOf
        (adjointGroup .E6 (fixSubfield σ))).map (fixedFieldInclusion σ) :
          Subgroup (adjointGroup .E6 K₂)) : Set (adjointGroup .E6 K₂))) =
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K₂).rootGroup J := by
  have : Finite (ModGL .E6 K₂) := finite_modGL
  set T₂ : Subgroup (adjointGroup .E6 K₂) :=
    ((leviTorus (fixSubfield σ) J).subgroupOf (adjointGroup .E6 (fixSubfield σ))).map
      (fixedFieldInclusion σ) with hT₂
  have hT : (T₂.map (adjointGroup .E6 K₂).subtype).subgroupOf (adjointGroup .E6 K₂) = T₂ :=
    Subgroup.comap_map_eq_self_of_injective (adjointGroup .E6 K₂).subtype_injective T₂
  have h := perfectCore_inf_centralizer_map_leviTorus_inf (fixSubfield σ).subtype hq hJ
  rw [← map_subtype_map_fixedFieldInclusion_leviTorus_E6 σ J, ← hT₂,
    F4Pilot.perfectCore_inf_centralizer_eq_map (map_subtype_le T₂), hT] at h
  rw [levi_adjDatumE6_eq]
  apply Subgroup.map_injective (adjointGroup .E6 K₂).subtype_injective
  rw [h, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_E6 _)]

end Model

section Gen


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_iSup_perfectCore_of_mem_normalizer_E6_cover (hset : StandardSetting G L)
    {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk : Nat.card (fixSubfield σ) = 2 ^ f) (hq : 4 ≤ Nat.card (fixSubfield σ))
    (e : L ≃* adjointGroup .E6 (fixSubfield σ)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M)))
    (eM : M ⧸ center M ≃* adjointGroup .E6 K₂) (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      perfectCore (M ⊓ centralizer (modelToG e (leviTorus (fixSubfield σ) J.1) : Set G)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : Finite (adjointGroup .E6 K₂) := by
    have : Finite (ModGL Tag.E6 K₂) := finite_modGL
    infer_instance
  obtain ⟨Φ, hΦ⟩ :=
    exists_mulEquiv_quotient_center_comp_fixedFieldInclusion hset hK₂ hσ hk e ht hKt hMp hZ eM htM
  have hML := (inf_centralizer_eq_of_mem_normalizer_E6_cover hset hk e ht hKt hMp hZ hK₂ eM
    htM).2
  have hLM : L ≤ M := hML ▸ inf_le_left
  have hTM : ∀ J : Finset (Fin (Tag.rank .E6)), modelToG e (leviTorus (fixSubfield σ) J) ≤ M :=
    fun J => (modelToG_le e _).trans hLM
  have hTπ : ∀ J : Finset (Fin (Tag.rank .E6)),
      ((modelToG e (leviTorus (fixSubfield σ) J)).subgroupOf M).map
          (QuotientGroup.mk' (center M)) =
        (((leviTorus (fixSubfield σ) J).subgroupOf (adjointGroup .E6 (fixSubfield σ))).map
          (fixedFieldInclusion σ)).map Φ.toMonoidHom := by
    intro J
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨x, hx, hxm⟩ := (mem_modelToG e).1 (mem_subgroupOf.1 hm)
      exact ⟨fixedFieldInclusion σ x, ⟨x, mem_subgroupOf.2 hx, rfl⟩, hΦ x m hxm.symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hxT : (⟨((e.symm x : L) : G), hLM (e.symm x).2⟩ : M) ∈
          (modelToG e (leviTorus (fixSubfield σ) J)).subgroupOf M :=
        mem_subgroupOf.2 (symm_mem_modelToG e (mem_subgroupOf.1 hx))
      exact ⟨_, hxT, (hΦ x _ rfl).symm⟩
  have hgenQ : ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      perfectCore (centralizer ((((modelToG e (leviTorus (fixSubfield σ) J.1)).subgroupOf M).map
        (QuotientGroup.mk' (center M)) : Subgroup (M ⧸ center M)) : Set (M ⧸ center M))) = ⊤ := by
    have h1 : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
        perfectCore (centralizer ((((modelToG e (leviTorus (fixSubfield σ) J.1)).subgroupOf M).map
          (QuotientGroup.mk' (center M)) : Subgroup (M ⧸ center M)) : Set (M ⧸ center M))) =
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K₂).rootGroup J.1).map Φ.toMonoidHom := by
      intro J
      rw [hTπ, ← F4Pilot.map_centralizer_mulEquiv, ← CFSG.Quasithin.map_perfectCore,
        perfectCore_centralizer_map_fixedFieldInclusion_leviTorus_E6 σ hq J.2]
    simp_rw [h1]
    rw [← Subgroup.map_iSup, iSup_levi_adjDatumE6_eq_top, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top]
    exact Φ.surjective
  have hmapTop : (⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      perfectCore (centralizer (((modelToG e (leviTorus (fixSubfield σ) J.1)).subgroupOf M :
        Subgroup M) : Set M))).map (QuotientGroup.mk' (center M)) = ⊤ := by
    rw [Subgroup.map_iSup, eq_top_iff, ← hgenQ]
    exact iSup_mono fun J => perfectCore_centralizer_map_le _
  have hMperf : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hTop := eq_top_of_map_eq_top_of_perfect hMperf.commutator_eq_top hmapTop
  intro g hg
  have hg' : (⟨g, hg⟩ : M) ∈ ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      perfectCore (centralizer (((modelToG e (leviTorus (fixSubfield σ) J.1)).subgroupOf M :
        Subgroup M) : Set M)) := hTop ▸ mem_top _
  have h2 := mem_map_of_mem M.subtype hg'
  rw [Subgroup.map_iSup] at h2
  simp_rw [← F4Pilot.perfectCore_inf_centralizer_eq_map (hTM _)] at h2
  exact h2

end Gen

section Input


theorem e6FieldRowStep3Input_holds : E6FieldRowStep3Input := by
  intro G _ _ L K₂ _ _ _ σ f hq hf e t hw _ hCT h htM _
  have hq4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hperf : ⁅pieceSup e, pieceSup e⁆ = pieceSup e :=
    Subgroup.isPerfect_iff.1 hCT.quasisimple.1
  obtain ⟨Ψ, -⟩ := hCT.quotient
  have hMp : ⁅CFSG.conjugate (pieceSup e) h, CFSG.conjugate (pieceSup e) h⁆ =
      CFSG.conjugate (pieceSup e) h := commutator_conjugate_eq hperf h
  have hZ : Odd (Nat.card (center (CFSG.conjugate (pieceSup e) h))) := by
    rw [card_center_conjugate]
    exact hCT.odd_card_center
  have hgen := le_iSup_perfectCore_of_mem_normalizer_E6_cover hw.standard hq.card_eq hq.apply_eq
    hw.card_eq hq4 e hw.orderOf_eq hw.inf_eq hMp hZ
    ((coverConjugateQuotientCenterEquiv (pieceSup e) h).symm.trans Ψ.symm) htM
  exact F4Pilot.eq_of_le_iSup_perfectCore hgen (fun J => pieceCore_le_pieceSup J)
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm)

end Input

end CFSG.SeitzReduction.E6Pilot
