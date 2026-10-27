module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviTori
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignCores
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

section Transport

variable {G : Type*} [Group G] {C : Type*} [Group C]

theorem inf_centralizer_map_eq_map_centralizer {ψ : C →* G} (hψ : Function.Injective ψ)
    (T' : Subgroup C) :
    ψ.range ⊓ centralizer ((T'.map ψ : Subgroup G) : Set G) =
      (centralizer (T' : Set C)).map ψ := by
  ext x
  constructor
  · rintro ⟨⟨c, rfl⟩, hc⟩
    refine ⟨c, mem_centralizer_iff.2 fun y hy => hψ ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hc (ψ y) ⟨y, hy, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hc y hy]

variable [Finite G] [Finite C]

theorem perfectCore_range_inf_centralizer_map {ψ : C →* G} (hψ : Function.Injective ψ)
    (T' : Subgroup C) :
    perfectCore (ψ.range ⊓ centralizer ((T'.map ψ : Subgroup G) : Set G)) =
      (perfectCore (centralizer (T' : Set C))).map ψ := by
  rw [inf_centralizer_map_eq_map_centralizer hψ, CFSG.Quasithin.map_perfectCore]

theorem range_le_iSup_perfectCore_of_iSup_eq_top {ψ : C →* G} (hψ : Function.Injective ψ)
    {ι : Type*} {T' : ι → Subgroup C}
    (hgen : ⨆ i, perfectCore (centralizer (T' i : Set C)) = ⊤) :
    ψ.range ≤ ⨆ i, perfectCore (ψ.range ⊓ centralizer (((T' i).map ψ : Subgroup G) : Set G)) := by
  simp_rw [perfectCore_range_inf_centralizer_map hψ]
  rw [← Subgroup.map_iSup, hgen, ← MonoidHom.range_eq_map]

end Transport

theorem modelToG_eq_map_symm {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) (H : Subgroup (ModGL .F4 K)) :
    modelToG e H = (H.subgroupOf (adjointGroup .F4 K)).map (L.subtype.comp e.symm.toMonoidHom) :=
  Subgroup.map_map _ _ _

section Model


variable {K : Type} [Field K] [Finite K]

theorem perfectCore_centralizer_leviTorus_subgroupOf (hq : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) :
    perfectCore (centralizer (((leviTorus K J).subgroupOf (adjointGroup .F4 K) :
        Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K))) =
      (rootSpan .F4 K (amalgamRoots J)).subgroupOf (adjointGroup .F4 K) := by
  have : Finite (ModGL .F4 K) := finite_modGL
  have h := perfectCore_inf_centralizer_leviTorus hq hJ
  rw [perfectCore_inf_centralizer_eq_map (leviTorus_le_adjointGroup J)] at h
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [h, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_F4 _)]

theorem iSup_perfectCore_centralizer_leviTorus_eq_top (hq : 4 ≤ Nat.card K) :
    ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore (centralizer (((leviTorus K J.1).subgroupOf (adjointGroup .F4 K) :
        Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K))) = ⊤ := by
  have hct := CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum K
  have hgen : ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).isFiniteType
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).divisible) hct
  rw [← hgen]
  refine iSup_congr fun J => ?_
  rw [perfectCore_centralizer_leviTorus_subgroupOf hq J.2]
  change _ = CFSG.LieType.CurtisTits.levi (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup J.1
  rw [levi_f4Datum_eq]

theorem range_le_iSup_perfectCore_leviTorus {G : Type} [Group G] [Finite G]
    (hq : 4 ≤ Nat.card K) {Φ : adjointGroup .F4 K →* G} (hΦ : Function.Injective Φ) :
    Φ.range ≤ ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore (Φ.range ⊓ centralizer
        ((((leviTorus K J.1).subgroupOf (adjointGroup .F4 K)).map Φ : Subgroup G) : Set G)) :=
  range_le_iSup_perfectCore_of_iSup_eq_top hΦ (iSup_perfectCore_centralizer_leviTorus_eq_top hq)

omit [Finite K]
  in
theorem map_subtype_map_fixedFieldInclusion_leviTorus {K₂ : Type} [Field K₂] (σ : K₂ ≃+* K₂)
    (J : Finset (Fin (Tag.rank .F4))) :
    (((leviTorus (fixSubfield σ) J).subgroupOf (adjointGroup .F4 (fixSubfield σ))).map
        (fixedFieldInclusion σ)).map (adjointGroup .F4 K₂).subtype =
      (leviTorus (fixSubfield σ) J).map (baseChangeGL (fixSubfield σ).subtype) := by
  rw [Subgroup.map_map]
  have h : (adjointGroup .F4 K₂).subtype.comp (fixedFieldInclusion σ) =
      (baseChangeGL (fixSubfield σ).subtype).comp (adjointGroup .F4 (fixSubfield σ)).subtype :=
    MonoidHom.ext fun g => coe_fixedFieldInclusion σ g
  rw [h, ← Subgroup.map_map, subgroupOf_map_subtype, inf_of_le_left (leviTorus_le_adjointGroup J)]

omit [Finite K]
  in
theorem perfectCore_centralizer_map_fixedFieldInclusion_leviTorus {K₂ : Type} [Field K₂]
    [Finite K₂] (σ : K₂ ≃+* K₂) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J.card ≤ 2) :
    perfectCore (centralizer ((((leviTorus (fixSubfield σ) J).subgroupOf
        (adjointGroup .F4 (fixSubfield σ))).map (fixedFieldInclusion σ) :
          Subgroup (adjointGroup .F4 K₂)) : Set (adjointGroup .F4 K₂))) =
      (rootSpan .F4 K₂ (amalgamRoots J)).subgroupOf (adjointGroup .F4 K₂) := by
  have : Finite (ModGL .F4 K₂) := finite_modGL
  set T₂ : Subgroup (adjointGroup .F4 K₂) :=
    ((leviTorus (fixSubfield σ) J).subgroupOf (adjointGroup .F4 (fixSubfield σ))).map
      (fixedFieldInclusion σ) with hT₂
  have hT : (T₂.map (adjointGroup .F4 K₂).subtype).subgroupOf (adjointGroup .F4 K₂) = T₂ :=
    Subgroup.comap_map_eq_self_of_injective (adjointGroup .F4 K₂).subtype_injective T₂
  have h := perfectCore_inf_centralizer_map_leviTorus (fixSubfield σ).subtype hq hJ
  rw [← map_subtype_map_fixedFieldInclusion_leviTorus σ J, ← hT₂,
    perfectCore_inf_centralizer_eq_map (map_subtype_le T₂), hT] at h
  apply Subgroup.map_injective (adjointGroup .F4 K₂).subtype_injective
  rw [h, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_F4 _)]

omit [Finite K] in
theorem iSup_perfectCore_centralizer_map_fixedFieldInclusion_eq_top {K₂ : Type} [Field K₂]
    [Finite K₂] (σ : K₂ ≃+* K₂) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore (centralizer ((((leviTorus (fixSubfield σ) J.1).subgroupOf
        (adjointGroup .F4 (fixSubfield σ))).map (fixedFieldInclusion σ) :
          Subgroup (adjointGroup .F4 K₂)) : Set (adjointGroup .F4 K₂))) = ⊤ := by
  have hct := CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum K₂
  have hgen : ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K₂).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K₂).isFiniteType
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K₂).divisible) hct
  rw [← hgen]
  refine iSup_congr fun J => ?_
  rw [perfectCore_centralizer_map_fixedFieldInclusion_leviTorus σ hq J.2]
  change _ = CFSG.LieType.CurtisTits.levi (CFSG.LieType.Steinberg.Adjoint.f4Datum K₂).rootGroup J.1
  rw [levi_f4Datum_eq]

omit [Finite K] in
theorem range_le_iSup_perfectCore_modelToG_of_comp_fixedFieldInclusion {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂] {σ : K₂ ≃+* K₂}
    (hq : 4 ≤ Nat.card (fixSubfield σ)) (e : L ≃* adjointGroup .F4 (fixSubfield σ))
    {Φ : adjointGroup .F4 K₂ →* G} (hΦ : Function.Injective Φ)
    (hcomp : ∀ x : adjointGroup .F4 (fixSubfield σ),
      Φ (fixedFieldInclusion σ x) = ((e.symm x : L) : G)) :
    Φ.range ≤ ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
      perfectCore (Φ.range ⊓ centralizer (modelToG e (leviTorus (fixSubfield σ) J.1) : Set G)) := by
  have hc : Φ.comp (fixedFieldInclusion σ) = L.subtype.comp e.symm.toMonoidHom :=
    MonoidHom.ext hcomp
  have hT : ∀ J : Finset (Fin (Tag.rank .F4)), modelToG e (leviTorus (fixSubfield σ) J) =
      (((leviTorus (fixSubfield σ) J).subgroupOf (adjointGroup .F4 (fixSubfield σ))).map
        (fixedFieldInclusion σ)).map Φ := fun J => by
    rw [modelToG_eq_map_symm, Subgroup.map_map, hc]
  simp_rw [hT]
  exact range_le_iSup_perfectCore_of_iSup_eq_top hΦ
    (iSup_perfectCore_centralizer_map_fixedFieldInclusion_eq_top σ hq)

end Model

end CFSG.SeitzReduction.F4Pilot
