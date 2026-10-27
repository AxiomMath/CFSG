module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTField
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.CurtisTits (IsCompatible IsUniversalCompletion)
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG)

local instance e7PilotCTFieldNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Recognition


variable (K : Type) [Field K]

theorem exists_surjective_of_isCompatible_e7 {G : Type} [Group G]
    (φ : ∀ J, (e7Datum K).leviAmalgam J →* G)
    (hφ : IsCompatible (e7Datum K).leviAmalgam φ) (hgen : ⨆ J, (φ J).range = ⊤)
    (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    ∃ ψ : e7Data_valid.minGroup K →* G, (∀ J (x : (e7Datum K).leviAmalgam J), ψ x = φ J x) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ center (e7Data_valid.minGroup K) := by
  have hct := e7Datum_isCTGroupDatum K
  have hext := e7Datum_steinbergExtras K
  have hgenK : ⨆ J, (e7Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem (e7Datum K).isFiniteType (e7Datum K).divisible) hct
  have hU : IsUniversalCompletion.{0, 0, 0} (e7Datum K).leviAmalgam :=
    (e7Datum K).isUniversalCompletion_of_steinbergPresentation hct
      (steinbergPresentation_of_extras hct hext)
  obtain ⟨ψ, hψ, hsurj, hker, -⟩ :=
    CFSG.LieType.CurtisTits.recognition_of_isUniversalCompletion hgenK
      (CFSG.LieType.CurtisTits.isQuasisimple_e7 K) hU φ hφ hgen hnt
  exact ⟨ψ, hψ, hsurj, hker⟩

end Recognition

section Isogeny


variable {K : Type} [Field K] [Finite K]

theorem map_e7Isogeny_levi (J : Finset (Fin (Tag.rank .E7))) :
    (CFSG.LieType.CurtisTits.levi (e7Datum K).rootGroup J).map (e7Isogeny K) =
      CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J := by
  simp only [CFSG.LieType.CurtisTits.levi, CFSG.LieType.CurtisTits.rankOne, Subgroup.map_iSup,
    Subgroup.map_sup]
  refine iSup_congr fun j => iSup_congr fun _ => ?_
  have h₁ := CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup K (isRoot_single .E7 j)
  have h₂ := CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup K
    (isRoot_neg_single .E7 j)
  exact congrArg₂ (· ⊔ ·) h₁ h₂

@[expose] noncomputable def leviIsogenyE7 (J : Finset (Fin (Tag.rank .E7))) :
    CFSG.LieType.CurtisTits.levi (e7Datum K).rootGroup J →*
      CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J :=
  ((e7Isogeny K).comp (Subgroup.subtype _)).codRestrict _ fun x => by
    rw [← map_e7Isogeny_levi J]
    exact ⟨x, x.2, rfl⟩

theorem coe_leviIsogenyE7 (J : Finset (Fin (Tag.rank .E7)))
    (x : CFSG.LieType.CurtisTits.levi (e7Datum K).rootGroup J) :
    ((leviIsogenyE7 J x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J) :
      adjointGroup .E7 K) = e7Isogeny K x :=
  rfl

theorem leviIsogenyE7_surjective (J : Finset (Fin (Tag.rank .E7))) :
    Function.Surjective (leviIsogenyE7 (K := K) J) := by
  rintro ⟨y, hy⟩
  rw [← map_e7Isogeny_levi J] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

variable {G : Type} [Group G]

@[expose] noncomputable def scFamilyE7 (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G)
    (J : {J : Finset (Fin (e7Datum K).rank) // J.card ≤ 2}) : (e7Datum K).leviAmalgam J →* G :=
  (φ J).comp (leviIsogenyE7 J.1)

theorem scFamilyE7_apply (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G)
    (J : {J : Finset (Fin (e7Datum K).rank) // J.card ≤ 2}) (x : (e7Datum K).leviAmalgam J) :
    scFamilyE7 φ J x = φ J (leviIsogenyE7 J.1 x) :=
  rfl

theorem isCompatible_scFamilyE7 {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G}
    (hφ : IsCompatible (adjDatumE7 K).leviAmalgam φ) :
    IsCompatible (e7Datum K).leviAmalgam (scFamilyE7 φ) := by
  intro i j hij x y hxy
  rw [scFamilyE7_apply, scFamilyE7_apply]
  refine hφ i j hij _ _ ?_
  rw [coe_leviIsogenyE7, coe_leviIsogenyE7]
  exact congrArg (e7Isogeny K) hxy

theorem range_scFamilyE7 (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G)
    (J : {J : Finset (Fin (e7Datum K).rank) // J.card ≤ 2}) :
    (scFamilyE7 φ J).range = (φ J).range := by
  rw [scFamilyE7, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (leviIsogenyE7_surjective J.1),
    ← MonoidHom.range_eq_map]

end Isogeny

section Generators


variable {k K : Type} [Field k] [Field K]

theorem exists_levi_adjDatumE7_baseChangeGL (ι : k →+* K)
    {J : Finset (Fin (Tag.rank .E7))} {x : adjointGroup .E7 k}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 k).rootGroup J) :
    ∃ y : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J,
      ((y : adjointGroup .E7 K) : ModGL .E7 K) = baseChangeGL ι (x : ModGL .E7 k) := by
  rw [levi_adjDatumE7_eq, mem_subgroupOf] at hx
  have h := F4Pilot.map_rootSpan_baseChangeGL_le ι (amalgamRoots J) ⟨_, hx, rfl⟩
  refine ⟨⟨⟨_, (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
    rootSpan .E7 K (amalgamRoots J) ≤ adjointGroup .E7 K) h⟩, ?_⟩, rfl⟩
  rw [levi_adjDatumE7_eq, mem_subgroupOf]
  exact h

theorem xElement_mem_levi_adjDatumE7 (i : Fin (Tag.rank .E7)) (c : k) :
    xElement i c ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 k).rootGroup {i} := by
  rw [levi_adjDatumE7_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .E7 k γ)
    (Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩ le_rfl
    (xUnit_mem_rootSubgroup i c)

theorem yElement_mem_levi_adjDatumE7 (i : Fin (Tag.rank .E7)) (c : k) :
    yElement i c ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 k).rootGroup {i} := by
  rw [levi_adjDatumE7_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .E7 k γ)
    (-Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inr rfl⟩ le_rfl
    (yUnit_mem_rootSubgroup i c)

theorem exists_ne_one_mem_levi_adjDatumE7 (i : Fin (Tag.rank .E7)) :
    ∃ u : adjointGroup .E7 k, u ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 k).rootGroup {i} ∧
      u ≠ 1 := by
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (CFSG.LieType.Steinberg.Adjoint.rootGroup_ne_bot (F := rootOperatorFamily .E7) (K := k)
      (isRoot_single .E7 i))
  refine ⟨u, ?_, fun h => hu1 (Subtype.ext h)⟩
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  exact mem_sup_left u.2

end Generators

section Sup

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

variable (e : L ≃* adjointGroup .E7 K)

@[expose] noncomputable def pieceSup : Subgroup G :=
  ⨆ J : {J : Finset (Fin (Tag.rank .E7)) // J.card ≤ 2}, pieceCore e J.1

variable {e}

theorem pieceCore_le_pieceSup (J : {J : Finset (Fin (Tag.rank .E7)) // J.card ≤ 2}) :
    pieceCore e J.1 ≤ pieceSup e :=
  le_iSup (fun J : {J : Finset (Fin (Tag.rank .E7)) // J.card ≤ 2} => pieceCore e J.1) J

theorem mem_normalizer_pieceSup {t : G} (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer ((pieceSup e : Subgroup G) : Set G) :=
  F4Pilot.mem_normalizer_iSup fun J => le_normalizer_pieceCore e ht J.1

end Sup

section Main


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E7 (fixSubfield σ))

structure IsCTFieldFamily (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (adjDatumE7 K).leviAmalgam φ
  range_eq : ∀ J, (φ J).range = pieceCore e J.1
  fix : ∀ J (x : adjointGroup .E7 (fixSubfield σ)),
    x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 (fixSubfield σ)).rootGroup J.1 →
    ∀ y : (adjDatumE7 K).leviAmalgam J, ((y : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E7 (fixSubfield σ)) →
      φ J y = ((e.symm x : L) : G)

variable {e}

theorem le_pieceSup_of_isCTFieldFamily {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G}
    (hφ : IsCTFieldFamily e φ) : L ≤ pieceSup e := by
  have hcard : ∀ i : Fin (Tag.rank .E7), ({i} : Finset (Fin (Tag.rank .E7))).card ≤ 2 :=
    fun i => by simp
  have key : ∀ (i : Fin (Tag.rank .E7)) (x : adjointGroup .E7 (fixSubfield σ)),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 (fixSubfield σ)).rootGroup {i} →
      ((e.symm x : L) : G) ∈ pieceSup e := by
    intro i x hx
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE7_baseChangeGL (K := K) (fixSubfield σ).subtype hx
    rw [← hφ.fix ⟨{i}, hcard i⟩ x hx y hy]
    exact pieceCore_le_pieceSup ⟨{i}, hcard i⟩ ((hφ.range_eq ⟨{i}, hcard i⟩) ▸ ⟨y, rfl⟩)
  have hle : (⊤ : Subgroup (adjointGroup .E7 (fixSubfield σ))) ≤
      (pieceSup e).comap (L.subtype.comp e.symm.toMonoidHom) := by
    rw [← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact key i _ (xElement_mem_levi_adjDatumE7 i c)
    · exact key i _ (yElement_mem_levi_adjDatumE7 i c)
  intro g hg
  have h := hle (mem_top (e ⟨g, hg⟩))
  simpa using h

theorem exists_injective_of_isCTFieldFamily [Finite K] [CharP K 2]
    {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G} (hφ : IsCTFieldFamily e φ) :
    ∃ ψ : adjointGroup .E7 K →* G, Function.Injective ψ ∧ ψ.range = pieceSup e ∧
      (∀ J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2},
        ((adjDatumE7 K).leviAmalgam J).map ψ = pieceCore e J.1) ∧
      ∀ x : adjointGroup .E7 (fixSubfield σ),
        ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
  have hcard : ∀ i : Fin (Tag.rank .E7), ({i} : Finset (Fin (Tag.rank .E7))).card ≤ 2 :=
    fun i => by simp
  set G₀ : Subgroup G := pieceSup e with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => pieceCore_le_pieceSup J ((hφ.range_eq J) ▸ ⟨x, rfl⟩)
  set φ' : ∀ J, (adjDatumE7 K).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (adjDatumE7 K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ.compatible i j hij x y hxy)
  have hrange' : ∀ J, (φ' J).range.map G₀.subtype = pieceCore e J.1 := fun J => by
    rw [← MonoidHom.range_comp]
    exact hφ.range_eq J
  have hφs : IsCompatible (e7Datum K).leviAmalgam (scFamilyE7 φ') := isCompatible_scFamilyE7 hφ'
  have hgen' : ⨆ J, (scFamilyE7 φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [range_scFamilyE7]
    exact hrange' J
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
  refine ⟨G₀.subtype.comp ψ₀, G₀.subtype_injective.comp hinj₀, ?_, fun J => ?_, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj₀, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · have h1 : (G₀.subtype.comp ψ₀).comp ((adjDatumE7 K).leviAmalgam J).subtype = φ J :=
      MonoidHom.ext fun x => hψφ J x
    rw [← hφ.range_eq J, ← h1, MonoidHom.range_comp, Subgroup.range_subtype]
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

theorem exists_mulEquiv_of_isCTFieldFamily [Finite K] [CharP K 2]
    {φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G} (hφ : IsCTFieldFamily e φ) :
    ∃ Ψ : adjointGroup .E7 K ≃* pieceSup e,
      (∀ x : adjointGroup .E7 (fixSubfield σ),
        ((Ψ (fixedFieldInclusion σ x) : pieceSup e) : G) = ((e.symm x : L) : G)) ∧
      ∀ J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2},
        (((adjDatumE7 K).leviAmalgam J).map Ψ.toMonoidHom).map (pieceSup e).subtype =
          pieceCore e J.1 := by
  obtain ⟨ψ, hinj, hrange, hJ, hfix⟩ := exists_injective_of_isCTFieldFamily hφ
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun x => hfix x,
    fun J => ?_⟩
  rw [← hJ J, Subgroup.map_map]
  rfl

end Main

end CFSG.SeitzReduction.E7Pilot
