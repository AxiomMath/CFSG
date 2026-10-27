module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.EvenSmallLie
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.SeitzReduction.OmegaPilot (OmegaCatalogueClausesAt)

local instance e7PilotQ2FieldRowCTNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section CT

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E7 (fixSubfield σ))

structure IsTwoFieldFamily (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (adjDatumE7 K).leviAmalgam φ
  fix : ∀ J (x : adjointGroup .E7 (fixSubfield σ)),
    x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 (fixSubfield σ)).rootGroup J.1 →
    ∀ y : (adjDatumE7 K).leviAmalgam J, ((y : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E7 (fixSubfield σ)) →
      φ J y = ((e.symm x : L) : G)

variable {e}

@[expose] noncomputable def familySup (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G) :
    Subgroup G :=
  ⨆ J, (φ J).range

theorem exists_injective_of_isTwoFieldFamily [Finite K] [CharP K 2]
    {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G} (hφ : IsTwoFieldFamily e φ) :
    ∃ ψ : adjointGroup .E7 K →* G, Function.Injective ψ ∧ ψ.range = familySup φ ∧
      (∀ J (y : (adjDatumE7 K).leviAmalgam J), ψ y = φ J y) ∧
      ∀ x : adjointGroup .E7 (fixSubfield σ),
        ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
  have hcard : ∀ i : Fin (Tag.rank .E7), ({i} : Finset (Fin (Tag.rank .E7))).card ≤ 2 :=
    fun i => by simp
  set G₀ : Subgroup G := familySup φ with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (adjDatumE7 K).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (adjDatumE7 K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ.compatible i j hij x y hxy)
  have hφs : IsCompatible (e7Datum K).leviAmalgam (scFamilyE7 φ') := isCompatible_scFamilyE7 hφ'
  have hgen' : ⨆ J, (scFamilyE7 φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [range_scFamilyE7, ← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, scFamilyE7 φ' J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE7 (k := fixSubfield σ) 0
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE7_baseChangeGL (K := K) (fixSubfield σ).subtype hu
    obtain ⟨y', hy'⟩ := leviIsogenyE7_surjective (K := K) {0} y
    refine ⟨⟨{0}, hcard 0⟩, y', fun h => hu1 ?_⟩
    have h1 : φ ⟨{0}, hcard 0⟩ (leviIsogenyE7 {0} y') = 1 := congrArg Subtype.val h
    rw [hy', hφ.fix ⟨{0}, hcard 0⟩ u hu y hy] at h1
    have h2 : e.symm u = 1 := Subtype.ext h1
    rw [← map_one e.symm] at h2
    exact e.symm.injective h2
  obtain ⟨ψs, hψs, hsurj, hker⟩ := exists_surjective_of_isCompatible_e7 K _ hφs hgen' hnt
  have hinjs : Function.Injective ψs := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (E8Pilot.center_minGroup_e7_eq_bot (K := K)).le
  set ε := E8Pilot.e7MinEquivAdjoint K with hε
  set ψ₀ : adjointGroup .E7 K →* G₀ := ψs.comp ε.symm.toMonoidHom with hψ₀
  have hinj₀ : Function.Injective ψ₀ := hinjs.comp ε.symm.injective
  have hsurj₀ : Function.Surjective ψ₀ := hsurj.comp ε.symm.surjective
  have hψφ' : ∀ J (y : (adjDatumE7 K).leviAmalgam J), ψ₀ y = φ' J y := by
    intro J y
    obtain ⟨x, rfl⟩ := leviIsogenyE7_surjective (K := K) J.1 y
    have hx : ε.symm (leviIsogenyE7 J.1 x : adjointGroup .E7 K) =
        (x : e7Data_valid.minGroup K) := by
      rw [MulEquiv.symm_apply_eq, hε, E8Pilot.e7MinEquivAdjoint_apply, coe_leviIsogenyE7]
    rw [hψ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
    exact hψs J x
  have hψφ : ∀ J (y : (adjDatumE7 K).leviAmalgam J), (G₀.subtype.comp ψ₀) y = φ J y :=
    fun J y => congrArg Subtype.val (hψφ' J y)
  refine ⟨G₀.subtype.comp ψ₀, G₀.subtype_injective.comp hinj₀, ?_, hψφ, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj₀, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · have key : ∀ (i : Fin (Tag.rank .E7)) (x : adjointGroup .E7 (fixSubfield σ)),
        x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 (fixSubfield σ)).rootGroup {i} →
        (G₀.subtype.comp ψ₀) (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
      intro i x hx
      obtain ⟨y, hy⟩ := exists_levi_adjDatumE7_baseChangeGL (K := K) (fixSubfield σ).subtype hx
      have hyx : (y : adjointGroup .E7 K) = fixedFieldInclusion σ x := Subtype.ext hy
      rw [← hyx]
      exact (hψφ ⟨{i}, hcard i⟩ y).trans (hφ.fix ⟨{i}, hcard i⟩ x hx y hy)
    have h := CFSG.LieType.Ree.adjointGroup_hom_ext
      (f := (G₀.subtype.comp ψ₀).comp (fixedFieldInclusion σ))
      (g := L.subtype.comp e.symm.toMonoidHom)
      (fun i c => key i _ (xElement_mem_levi_adjDatumE7 i c))
      (fun i c => key i _ (yElement_mem_levi_adjDatumE7 i c))
    exact DFunLike.congr_fun h x

theorem le_familySup_of_isTwoFieldFamily [Finite K] [CharP K 2]
    {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G} (hφ : IsTwoFieldFamily e φ) :
    L ≤ familySup φ := by
  obtain ⟨ψ, -, hrange, -, hfix⟩ := exists_injective_of_isTwoFieldFamily hφ
  intro g hg
  rw [← hrange]
  refine ⟨fixedFieldInclusion σ (e ⟨g, hg⟩), ?_⟩
  rw [hfix, MulEquiv.symm_apply_apply]

theorem nonempty_mulEquiv_familySup [Finite K] [CharP K 2]
    {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G} (hφ : IsTwoFieldFamily e φ) :
    Nonempty (familySup φ ≃* adjointGroup .E7 K) := by
  obtain ⟨ψ, hinj, hrange, -, -⟩ := exists_injective_of_isTwoFieldFamily hφ
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem le_normalizer_familySup {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G} {C : Subgroup G}
    (h : ∀ J, C ≤ normalizer ((φ J).range : Set G)) :
    C ≤ normalizer ((familySup φ : Subgroup G) : Set G) :=
  fun _ hc => F4Pilot.mem_normalizer_iSup fun J => h J hc

end CT

section Input

@[expose] def E7TwoFieldRowFamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (e : L ≃* adjointGroup .E7 K) (t : G), E7Work L K t 1 → HR8FieldE7Two e t 1 →
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : CharP K₂ 2) (σ : K₂ ≃+* K₂)
      (e' : L ≃* adjointGroup .E7 (fixSubfield σ))
      (φ : ∀ J, (adjDatumE7 K₂).leviAmalgam J →* G),
      Nat.card K₂ = 2 ^ (2 * 1) ∧ IsTwoFieldFamily e' φ ∧
        ∀ J, centralizer (L : Set G) ≤ normalizer ((φ J).range : Set G)

theorem e7TwoFieldRowCTInput_of_family (h : E7TwoFieldRowFamilyInput) : E7TwoFieldRowCTInput := by
  intro G _ _ L K _ e t hw hF
  obtain ⟨K₂, _, _, _, σ, e', φ, hK₂, hφ, hN⟩ := h G L K e t hw hF
  obtain ⟨e₀⟩ := nonempty_mulEquiv_familySup hφ
  exact ⟨K₂, inferInstance, familySup φ, hK₂, ⟨e₀⟩, le_familySup_of_isTwoFieldFamily hφ,
    le_normalizer_familySup hN⟩

end Input

end CFSG.SeitzReduction.E7Pilot
