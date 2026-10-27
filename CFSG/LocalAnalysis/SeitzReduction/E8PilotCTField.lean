module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldFamily
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTField

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.CurtisTits (IsCompatible IsUniversalCompletion)
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG)

local instance e8PilotCTFieldNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Recognition


variable (K : Type) [Field K]

theorem exists_surjective_of_isCompatible_e8 {G : Type} [Group G]
    (φ : ∀ J, (adjDatumE8 K).leviAmalgam J →* G)
    (hφ : IsCompatible (adjDatumE8 K).leviAmalgam φ) (hgen : ⨆ J, (φ J).range = ⊤)
    (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    ∃ ψ : adjointGroup .E8 K →* G, (∀ J (x : (adjDatumE8 K).leviAmalgam J), ψ x = φ J x) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ center (adjointGroup .E8 K) := by
  have hct := Adjoint.e8_isCTGroupDatum K
  have hext := Adjoint.e8_steinbergExtras K
  have hgenK : ⨆ J, (adjDatumE8 K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem (adjDatumE8 K).isFiniteType
        (adjDatumE8 K).divisible) hct
  have hU : IsUniversalCompletion.{0, 0, 0} (adjDatumE8 K).leviAmalgam :=
    (adjDatumE8 K).isUniversalCompletion_of_steinbergPresentation hct
      (steinbergPresentation_of_extras hct hext)
  obtain ⟨ψ, hψ, hsurj, hker, -⟩ :=
    CFSG.LieType.CurtisTits.recognition_of_isUniversalCompletion hgenK
      (Adjoint.isQuasisimple_e8 K) hU φ hφ hgen hnt
  exact ⟨ψ, hψ, hsurj, hker⟩

end Recognition

section Generators


variable {k K : Type} [Field k] [Field K]

theorem exists_levi_adjDatumE8_baseChangeGL (ι : k →+* K)
    {J : Finset (Fin (Tag.rank .E8))} {x : adjointGroup .E8 k}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 k).rootGroup J) :
    ∃ y : CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J,
      ((y : adjointGroup .E8 K) : ModGL .E8 K) = baseChangeGL ι (x : ModGL .E8 k) := by
  rw [levi_adjDatumE8_eq, mem_subgroupOf] at hx
  have h := F4Pilot.map_rootSpan_baseChangeGL_le ι (amalgamRoots J) ⟨_, hx, rfl⟩
  refine ⟨⟨⟨_, rootSpan_le_adjointGroup_E8 _ h⟩, ?_⟩, rfl⟩
  rw [levi_adjDatumE8_eq, mem_subgroupOf]
  exact h

theorem xElement_mem_levi_adjDatumE8 (i : Fin (Tag.rank .E8)) (c : k) :
    xElement i c ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 k).rootGroup {i} := by
  rw [levi_adjDatumE8_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .E8 k γ)
    (Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩ le_rfl
    (xUnit_mem_rootSubgroup i c)

theorem yElement_mem_levi_adjDatumE8 (i : Fin (Tag.rank .E8)) (c : k) :
    yElement i c ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 k).rootGroup {i} := by
  rw [levi_adjDatumE8_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .E8 k γ)
    (-Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inr rfl⟩ le_rfl
    (yUnit_mem_rootSubgroup i c)

theorem exists_ne_one_mem_levi_adjDatumE8 (i : Fin (Tag.rank .E8)) :
    ∃ u : adjointGroup .E8 k, u ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 k).rootGroup {i} ∧
      u ≠ 1 := by
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (CFSG.LieType.Steinberg.Adjoint.rootGroup_ne_bot (F := rootOperatorFamily .E8) (K := k)
      (isRoot_single .E8 i))
  refine ⟨u, ?_, fun h => hu1 (Subtype.ext h)⟩
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  exact mem_sup_left u.2

end Generators

section Sup

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

variable (e : L ≃* adjointGroup .E8 K)

@[expose] noncomputable def pieceSup : Subgroup G :=
  ⨆ J : {J : Finset (Fin (Tag.rank .E8)) // J.card ≤ 2}, pieceCore e J.1

variable {e}

theorem pieceCore_le_pieceSup (J : {J : Finset (Fin (Tag.rank .E8)) // J.card ≤ 2}) :
    pieceCore e J.1 ≤ pieceSup e :=
  le_iSup (fun J : {J : Finset (Fin (Tag.rank .E8)) // J.card ≤ 2} => pieceCore e J.1) J

theorem mem_normalizer_pieceSup {t : G} (ht : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer ((pieceSup e : Subgroup G) : Set G) :=
  F4Pilot.mem_normalizer_iSup fun J => le_normalizer_pieceCore e ht J.1

end Sup

section Main


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

theorem le_pieceSup_of_isFieldRowFamily {φ : ∀ J, (adjDatumE8 K).leviAmalgam J →* G}
    (hφ : IsFieldRowFamily e φ) : L ≤ pieceSup e := by
  have hcard : ∀ i : Fin (Tag.rank .E8), ({i} : Finset (Fin (Tag.rank .E8))).card ≤ 2 :=
    fun i => by simp
  have key : ∀ (i : Fin (Tag.rank .E8)) (x : adjointGroup .E8 (fixSubfield σ)),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 (fixSubfield σ)).rootGroup {i} →
      ((e.symm x : L) : G) ∈ pieceSup e := by
    intro i x hx
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE8_baseChangeGL (K := K) (fixSubfield σ).subtype hx
    rw [← hφ.fix ⟨{i}, hcard i⟩ x hx y hy]
    exact pieceCore_le_pieceSup ⟨{i}, hcard i⟩ ((hφ.range_eq ⟨{i}, hcard i⟩) ▸ ⟨y, rfl⟩)
  have hle : (⊤ : Subgroup (adjointGroup .E8 (fixSubfield σ))) ≤
      (pieceSup e).comap (L.subtype.comp e.symm.toMonoidHom) := by
    rw [← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact key i _ (xElement_mem_levi_adjDatumE8 i c)
    · exact key i _ (yElement_mem_levi_adjDatumE8 i c)
  intro g hg
  have h := hle (mem_top (e ⟨g, hg⟩))
  simpa using h

theorem exists_injective_of_isFieldRowFamily {φ : ∀ J, (adjDatumE8 K).leviAmalgam J →* G}
    (hφ : IsFieldRowFamily e φ) :
    ∃ ψ : adjointGroup .E8 K →* G, Function.Injective ψ ∧ ψ.range = pieceSup e ∧
      (∀ J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2},
        ((adjDatumE8 K).leviAmalgam J).map ψ = pieceCore e J.1) ∧
      ∀ x : adjointGroup .E8 (fixSubfield σ), ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
  have hcard : ∀ i : Fin (Tag.rank .E8), ({i} : Finset (Fin (Tag.rank .E8))).card ≤ 2 :=
    fun i => by simp
  set G₀ : Subgroup G := pieceSup e with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => pieceCore_le_pieceSup J ((hφ.range_eq J) ▸ ⟨x, rfl⟩)
  set φ' : ∀ J, (adjDatumE8 K).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (adjDatumE8 K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ.compatible i j hij x y hxy)
  have hrange' : ∀ J, (φ' J).range.map G₀.subtype = pieceCore e J.1 := fun J => by
    rw [← MonoidHom.range_comp]
    exact hφ.range_eq J
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact (iSup_congr fun J => hrange' J).trans hG₀.symm
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE8 (k := fixSubfield σ) 0
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE8_baseChangeGL (K := K) (fixSubfield σ).subtype hu
    refine ⟨⟨{0}, hcard 0⟩, y, fun h => hu1 ?_⟩
    have h1 : φ ⟨{0}, hcard 0⟩ y = 1 := congrArg Subtype.val h
    rw [hφ.fix ⟨{0}, hcard 0⟩ u hu y hy] at h1
    have h2 : e.symm u = 1 := Subtype.ext h1
    rw [← map_one e.symm] at h2
    exact e.symm.injective h2
  obtain ⟨ψ₀, hψ₀, hsurj, hker⟩ := exists_surjective_of_isCompatible_e8 K φ' hφ' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot_field .E8 K).le
  have hψφ : ∀ J (x : (adjDatumE8 K).leviAmalgam J), (G₀.subtype.comp ψ₀) x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  refine ⟨G₀.subtype.comp ψ₀, G₀.subtype_injective.comp hinj₀, ?_, fun J => ?_, fun x => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · have h1 : (G₀.subtype.comp ψ₀).comp ((adjDatumE8 K).leviAmalgam J).subtype = φ J :=
      MonoidHom.ext fun x => hψφ J x
    rw [← hφ.range_eq J, ← h1, MonoidHom.range_comp, Subgroup.range_subtype]
  · have key : ∀ (i : Fin (Tag.rank .E8)) (x : adjointGroup .E8 (fixSubfield σ)),
        x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 (fixSubfield σ)).rootGroup {i} →
        (G₀.subtype.comp ψ₀) (fixedFieldInclusion σ x) = ((e.symm x : L) : G) := by
      intro i x hx
      obtain ⟨y, hy⟩ := exists_levi_adjDatumE8_baseChangeGL (K := K) (fixSubfield σ).subtype hx
      have hyx : (y : adjointGroup .E8 K) = fixedFieldInclusion σ x := Subtype.ext hy
      rw [← hyx]
      exact (hψφ ⟨{i}, hcard i⟩ y).trans (hφ.fix ⟨{i}, hcard i⟩ x hx y hy)
    have h := CFSG.LieType.Ree.adjointGroup_hom_ext
      (f := (G₀.subtype.comp ψ₀).comp (fixedFieldInclusion σ))
      (g := L.subtype.comp e.symm.toMonoidHom)
      (fun i c => key i _ (xElement_mem_levi_adjDatumE8 i c))
      (fun i c => key i _ (yElement_mem_levi_adjDatumE8 i c))
    exact DFunLike.congr_fun h x

theorem exists_mulEquiv_of_isFieldRowFamily {φ : ∀ J, (adjDatumE8 K).leviAmalgam J →* G}
    (hφ : IsFieldRowFamily e φ) :
    ∃ Ψ : adjointGroup .E8 K ≃* pieceSup e,
      (∀ x : adjointGroup .E8 (fixSubfield σ),
        ((Ψ (fixedFieldInclusion σ x) : pieceSup e) : G) = ((e.symm x : L) : G)) ∧
      ∀ J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2},
        (((adjDatumE8 K).leviAmalgam J).map Ψ.toMonoidHom).map (pieceSup e).subtype =
          pieceCore e J.1 := by
  obtain ⟨ψ, hinj, hrange, hJ, hfix⟩ := exists_injective_of_isFieldRowFamily hφ
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun x => hfix x,
    fun J => ?_⟩
  rw [← hJ J, Subgroup.map_map]
  rfl

end Main

section FromHR8


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

theorem exists_mulEquiv_fieldRow_of_neighbour
    (hψ : Nonempty (E8Neighbour.high.levi K ≃* neighbourCore e .high)) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) (hσ : orderOf σ = 2)
    (hfix : perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E8Neighbour.high.levi (fixSubfield σ)).map
        (adjointGroup .E8 (fixSubfield σ)).subtype))
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ Ψ : adjointGroup .E8 K ≃* pieceSup e,
      (∀ x : adjointGroup .E8 (fixSubfield σ),
        ((Ψ (fixedFieldInclusion σ x) : pieceSup e) : G) = ((e.symm x : L) : G)) ∧
      ∀ J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2},
        (((adjDatumE8 K).leviAmalgam J).map Ψ.toMonoidHom).map (pieceSup e).subtype =
          pieceCore e J.1 := by
  obtain ⟨φ, hφ⟩ := exists_isFieldRowFamily hψ htL ht2 hσ hfix hq
  exact exists_mulEquiv_of_isFieldRowFamily hφ

theorem le_pieceSup_fieldRow_of_neighbour
    (hψ : Nonempty (E8Neighbour.high.levi K ≃* neighbourCore e .high)) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) (hσ : orderOf σ = 2)
    (hfix : perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E8Neighbour.high.levi (fixSubfield σ)).map
        (adjointGroup .E8 (fixSubfield σ)).subtype))
    (hq : 4 ≤ Nat.card (fixSubfield σ)) : L ≤ pieceSup e := by
  obtain ⟨φ, hφ⟩ := exists_isFieldRowFamily hψ htL ht2 hσ hfix hq
  exact le_pieceSup_of_isFieldRowFamily hφ

end FromHR8

end CFSG.SeitzReduction.E8Pilot
