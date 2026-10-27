module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.CurtisTits (IsCompatible IsUniversalCompletion)
open CFSG.Quasithin (perfectCore)

local instance e6PilotCTFieldNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Recognition


variable (K : Type) [Field K]

theorem exists_surjective_of_isCompatible_e6 {G : Type} [Group G]
    (φ : ∀ J, (e6Datum K).leviAmalgam J →* G)
    (hφ : IsCompatible (e6Datum K).leviAmalgam φ) (hgen : ⨆ J, (φ J).range = ⊤)
    (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    ∃ ψ : e6Data_valid.minGroup K →* G, (∀ J (x : (e6Datum K).leviAmalgam J), ψ x = φ J x) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ center (e6Data_valid.minGroup K) ∧ CFSG.IsQuasisimple G ∧
      center G = (center (e6Data_valid.minGroup K)).map ψ := by
  have hct := e6Datum_isCTGroupDatum K
  have hext := e6Datum_steinbergExtras K
  have hgenK : ⨆ J, (e6Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem (e6Datum K).isFiniteType (e6Datum K).divisible) hct
  have hU : IsUniversalCompletion.{0, 0, 0} (e6Datum K).leviAmalgam :=
    (e6Datum K).isUniversalCompletion_of_steinbergPresentation hct
      (steinbergPresentation_of_extras hct hext)
  obtain ⟨ψ, hψ, hsurj, hker, hq, hZ, -⟩ :=
    CFSG.LieType.CurtisTits.recognition_of_isUniversalCompletion hgenK
      (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) hU φ hφ hgen hnt
  exact ⟨ψ, hψ, hsurj, hker, hq, hZ⟩

end Recognition

section Isogeny


variable {K : Type} [Field K] [Finite K]

theorem map_e6Isogeny_levi (J : Finset (Fin (Tag.rank .E6))) :
    (CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup J).map (e6Isogeny K) =
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J := by
  simp only [CFSG.LieType.CurtisTits.levi, CFSG.LieType.CurtisTits.rankOne, Subgroup.map_iSup,
    Subgroup.map_sup]
  refine iSup_congr fun j => iSup_congr fun _ => ?_
  have h₁ := CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup K (isRoot_single .E6 j)
  have h₂ := CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup K
    (isRoot_neg_single .E6 j)
  exact congrArg₂ (· ⊔ ·) h₁ h₂

@[expose] noncomputable def leviIsogeny (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup J →*
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J :=
  ((e6Isogeny K).comp (Subgroup.subtype _)).codRestrict _ fun x => by
    rw [← map_e6Isogeny_levi J]
    exact ⟨x, x.2, rfl⟩

theorem coe_leviIsogeny (J : Finset (Fin (Tag.rank .E6)))
    (x : CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup J) :
    ((leviIsogeny J x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
      adjointGroup .E6 K) = e6Isogeny K x :=
  rfl

theorem leviIsogeny_surjective (J : Finset (Fin (Tag.rank .E6))) :
    Function.Surjective (leviIsogeny (K := K) J) := by
  rintro ⟨y, hy⟩
  rw [← map_e6Isogeny_levi J] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem ker_e6Isogeny_eq_center :
    (e6Isogeny K).ker = center (e6Data_valid.minGroup K) := by
  refine le_antisymm (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) (e6Isogeny_ne_one K)) fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hzc : e6Isogeny K z ∈ center (adjointGroup .E6 K) := mem_center_iff.2 fun a => by
    obtain ⟨g, rfl⟩ := e6Isogeny_surjective K a
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hz g)]
  rw [center_adjointGroup_eq_bot, mem_bot] at hzc
  exact hzc

@[expose] noncomputable def centerQuotientIsogenyEquiv :
    e6Data_valid.minGroup K ⧸ center (e6Data_valid.minGroup K) ≃* adjointGroup .E6 K :=
  (QuotientGroup.quotientMulEquivOfEq ker_e6Isogeny_eq_center.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (e6Isogeny_surjective K))

theorem centerQuotientIsogenyEquiv_mk
    (x : e6Data_valid.minGroup K) :
    centerQuotientIsogenyEquiv (QuotientGroup.mk x) = e6Isogeny K x :=
  rfl

end Isogeny

section Family


variable {K : Type} [Field K] [Finite K] {G : Type} [Group G]

@[expose] noncomputable def scFamily (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G)
    (J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}) : (e6Datum K).leviAmalgam J →* G :=
  (φ J).comp (leviIsogeny J.1)

theorem scFamily_apply (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G)
    (J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}) (x : (e6Datum K).leviAmalgam J) :
    scFamily φ J x = φ J (leviIsogeny J.1 x) :=
  rfl

theorem isCompatible_scFamily {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsCompatible (adjDatumE6 K).leviAmalgam φ) :
    IsCompatible (e6Datum K).leviAmalgam (scFamily φ) := by
  intro i j hij x y hxy
  rw [scFamily_apply, scFamily_apply]
  refine hφ i j hij _ _ ?_
  rw [coe_leviIsogeny, coe_leviIsogeny]
  exact congrArg (e6Isogeny K) hxy

theorem range_scFamily (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G)
    (J : {J : Finset (Fin (e6Datum K).rank) // J.card ≤ 2}) :
    (scFamily φ J).range = (φ J).range := by
  rw [scFamily, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (leviIsogeny_surjective J.1),
    ← MonoidHom.range_eq_map]

end Family

section Generators


variable {k K : Type} [Field k] [Field K]

theorem exists_levi_adjDatumE6_baseChangeGL (ι : k →+* K)
    {J : Finset (Fin (Tag.rank .E6))} {x : adjointGroup .E6 k}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup J) :
    ∃ y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J,
      ((y : adjointGroup .E6 K) : ModGL .E6 K) = baseChangeGL ι (x : ModGL .E6 k) := by
  rw [levi_adjDatumE6_eq, mem_subgroupOf] at hx
  have h := F4Pilot.map_rootSpan_baseChangeGL_le ι (amalgamRoots J) ⟨_, hx, rfl⟩
  refine ⟨⟨⟨_, rootSpan_le_adjointGroup_E6 _ h⟩, ?_⟩, rfl⟩
  rw [levi_adjDatumE6_eq, mem_subgroupOf]
  exact h

theorem xElement_mem_levi_adjDatumE6 (i : Fin (Tag.rank .E6)) (c : k) :
    xElement i c ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i} := by
  rw [levi_adjDatumE6_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .E6 k γ)
    (Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inl rfl⟩ le_rfl
    (xUnit_mem_rootSubgroup i c)

theorem yElement_mem_levi_adjDatumE6 (i : Fin (Tag.rank .E6)) (c : k) :
    yElement i c ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i} := by
  rw [levi_adjDatumE6_eq, mem_subgroupOf]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ amalgamRoots {i}) => rootSubgroup .E6 k γ)
    (-Pi.single i 1) ⟨i, Finset.mem_singleton_self i, Or.inr rfl⟩ le_rfl
    (yUnit_mem_rootSubgroup i c)

theorem exists_ne_one_mem_levi_adjDatumE6 (i : Fin (Tag.rank .E6)) :
    ∃ u : adjointGroup .E6 k, u ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i} ∧
      u ≠ 1 := by
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (CFSG.LieType.Steinberg.Adjoint.rootGroup_ne_bot (F := rootOperatorFamily .E6) (K := k)
      (isRoot_single .E6 i))
  refine ⟨u, ?_, fun h => hu1 (Subtype.ext h)⟩
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  exact mem_sup_left u.2

end Generators

section Sup

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E6 (fixSubfield σ))

@[expose] noncomputable def pieceSup : Subgroup G :=
  ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, pieceCore e J.1

variable {e}

theorem pieceCore_le_pieceSup (J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}) :
    pieceCore e J.1 ≤ pieceSup e :=
  le_iSup (fun J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} => pieceCore e J.1) J

end Sup

section CenterQuotient

variable {X Y : Type*} [Group X] [Group Y]

@[expose] noncomputable def centerQuotientMulEquiv (ψ : X →* Y) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ center X) (hZ : center Y = (center X).map ψ) :
    X ⧸ center X ≃* Y ⧸ center Y :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ,
        Subgroup.comap_map_eq_self (by simpa using hker)] :
      ((QuotientGroup.mk' (center Y)).comp ψ).ker = center X).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hsurj))

theorem centerQuotientMulEquiv_mk (ψ : X →* Y) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ center X) (hZ : center Y = (center X).map ψ) (x : X) :
    centerQuotientMulEquiv ψ hsurj hker hZ (QuotientGroup.mk x) = QuotientGroup.mk (ψ x) :=
  rfl

end CenterQuotient

section Main


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E6 (fixSubfield σ))

structure IsScFieldRowFamily (φ : ∀ J, (e6Datum K).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (e6Datum K).leviAmalgam φ
  range_eq : ∀ J, (φ J).range = pieceCore e J.1
  fix : ∀ J (x : adjointGroup .E6 (fixSubfield σ)),
    x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1 →
    ∀ y : (e6Datum K).leviAmalgam J, ((e6Isogeny K y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ)) →
      φ J y = ((e.symm x : L) : G)

structure IsFieldRowFamily (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (adjDatumE6 K).leviAmalgam φ
  range_eq : ∀ J, (φ J).range = pieceCore e J.1
  fix : ∀ J (x : adjointGroup .E6 (fixSubfield σ)),
    x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1 →
    ∀ y : (adjDatumE6 K).leviAmalgam J, ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ)) →
      φ J y = ((e.symm x : L) : G)

variable {e}

theorem IsFieldRowFamily.isScFieldRowFamily {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsFieldRowFamily e φ) : IsScFieldRowFamily e (scFamily φ) where
  compatible := isCompatible_scFamily hφ.compatible
  range_eq J := (range_scFamily φ J).trans (hφ.range_eq J)
  fix J x hx y hxy := hφ.fix J x hx _ (by rw [coe_leviIsogeny]; exact hxy)

theorem le_pieceSup_of_isScFieldRowFamily {φ : ∀ J, (e6Datum K).leviAmalgam J →* G}
    (hφ : IsScFieldRowFamily e φ) : L ≤ pieceSup e := by
  have hcard : ∀ i : Fin (Tag.rank .E6), ({i} : Finset (Fin (Tag.rank .E6))).card ≤ 2 :=
    fun i => by simp
  have key : ∀ (i : Fin (Tag.rank .E6)) (x : adjointGroup .E6 (fixSubfield σ)),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup {i} →
      ((e.symm x : L) : G) ∈ pieceSup e := by
    intro i x hx
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype hx
    obtain ⟨y', rfl⟩ := leviIsogeny_surjective (K := K) {i} y
    rw [← hφ.fix ⟨{i}, hcard i⟩ x hx y' hy]
    exact pieceCore_le_pieceSup ⟨{i}, hcard i⟩ ((hφ.range_eq ⟨{i}, hcard i⟩) ▸ ⟨y', rfl⟩)
  have hle : (⊤ : Subgroup (adjointGroup .E6 (fixSubfield σ))) ≤
      (pieceSup e).comap (L.subtype.comp e.symm.toMonoidHom) := by
    rw [← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact key i _ (xElement_mem_levi_adjDatumE6 i c)
    · exact key i _ (yElement_mem_levi_adjDatumE6 i c)
  intro g hg
  have h := hle (mem_top (e ⟨g, hg⟩))
  simpa using h

theorem exists_surjective_pieceSup_of_isScFieldRowFamily
    {φ : ∀ J, (e6Datum K).leviAmalgam J →* G} (hφ : IsScFieldRowFamily e φ) :
    ∃ ψ : e6Data_valid.minGroup K →* pieceSup e,
      Function.Surjective ψ ∧ ψ.ker ≤ center (e6Data_valid.minGroup K) ∧
      center (pieceSup e) = (center (e6Data_valid.minGroup K)).map ψ ∧
      (∀ J (y : (e6Datum K).leviAmalgam J), ((ψ y : pieceSup e) : G) = φ J y) ∧
      (∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
        ((CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup J.1).map ψ).map (pieceSup e).subtype =
          pieceCore e J.1) ∧
      ∀ J (x : adjointGroup .E6 (fixSubfield σ)),
        x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1 →
        ∀ y : (e6Datum K).leviAmalgam J, ((e6Isogeny K y : adjointGroup .E6 K) : ModGL .E6 K) =
          baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ)) →
          ((ψ y : pieceSup e) : G) = ((e.symm x : L) : G) := by
  have hcard : ∀ i : Fin (Tag.rank .E6), ({i} : Finset (Fin (Tag.rank .E6))).card ≤ 2 :=
    fun i => by simp
  set G₀ := pieceSup e with hG₀
  have hle : ∀ J y, φ J y ∈ G₀ := fun J y => pieceCore_le_pieceSup J
    ((hφ.range_eq J) ▸ ⟨y, rfl⟩)
  set φ' : ∀ J, (e6Datum K).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (e6Datum K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ.compatible i j hij x y hxy)
  have hrange' : ∀ J, (φ' J).range.map G₀.subtype = pieceCore e J.1 := fun J => by
    rw [← MonoidHom.range_comp]
    exact hφ.range_eq J
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact (iSup_congr fun J => hrange' J).trans hG₀.symm
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE6 (k := fixSubfield σ) 0
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype hu
    obtain ⟨y', rfl⟩ := leviIsogeny_surjective (K := K) {0} y
    refine ⟨⟨{0}, hcard 0⟩, y', fun h => hu1 ?_⟩
    have h1 : φ ⟨{0}, hcard 0⟩ y' = 1 := congrArg Subtype.val h
    rw [hφ.fix ⟨{0}, hcard 0⟩ u hu _ hy] at h1
    have h2 : e.symm u = 1 := Subtype.ext h1
    rw [← map_one e.symm] at h2
    exact e.symm.injective h2
  obtain ⟨ψ, hψ, hsurj, hker, -, hZ⟩ := exists_surjective_of_isCompatible_e6 K φ' hφ' hgen' hnt
  have hψφ : ∀ J (y : (e6Datum K).leviAmalgam J), ((ψ y : G₀) : G) = φ J y :=
    fun J y => congrArg Subtype.val (hψ J y)
  refine ⟨ψ, hsurj, hker, hZ, hψφ, fun J => ?_, fun J x hx y hxy => ?_⟩
  · have h : (CFSG.LieType.CurtisTits.levi (e6Datum K).rootGroup J.1).map ψ = (φ' J).range := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, (hψ J ⟨y, hy⟩).symm⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, hψ J y⟩
    rw [h, hrange' J]
  · rw [hψφ]
    exact hφ.fix J x hx y hxy

theorem isQuasisimple_pieceSup_of_isScFieldRowFamily
    {φ : ∀ J, (e6Datum K).leviAmalgam J →* G} (hφ : IsScFieldRowFamily e φ) :
    CFSG.IsQuasisimple (pieceSup e) := by
  obtain ⟨ψ, hsurj, hker, -⟩ := exists_surjective_pieceSup_of_isScFieldRowFamily hφ
  have hnt : ∃ s, ψ s ≠ 1 := by
    by_contra h
    push Not at h
    have htop : ψ.ker = ⊤ := eq_top_iff.2 fun s _ => h s
    have hZ : center (e6Data_valid.minGroup K) = ⊤ := eq_top_iff.2 (htop ▸ hker)
    obtain ⟨-, hsimple, -⟩ := CFSG.LieType.CurtisTits.isQuasisimple_e6 K
    have hsub : Subsingleton (e6Data_valid.minGroup K ⧸ center (e6Data_valid.minGroup K)) := by
      rw [hZ]
      exact QuotientGroup.subsingleton_quotient_top
    have := hsimple.toNontrivial
    exact not_subsingleton _ hsub
  exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) hsurj hnt

theorem exists_mulEquiv_center_quotient_of_isScFieldRowFamily
    {φ : ∀ J, (e6Datum K).leviAmalgam J →* G} (hφ : IsScFieldRowFamily e φ) :
    ∃ Ψ : adjointGroup .E6 K ≃* (pieceSup e ⧸ center (pieceSup e)),
      ∀ (x : adjointGroup .E6 (fixSubfield σ)) (g : pieceSup e), (g : G) = ((e.symm x : L) : G) →
        Ψ (fixedFieldInclusion σ x) = QuotientGroup.mk g := by
  obtain ⟨ψ, hsurj, hker, hZ, -, -, hfix⟩ := exists_surjective_pieceSup_of_isScFieldRowFamily hφ
  set Ψ := (centerQuotientIsogenyEquiv (K := K)).symm.trans
    (centerQuotientMulEquiv ψ hsurj hker hZ) with hΨ
  have hΨθ : ∀ s, Ψ (e6Isogeny K s) = QuotientGroup.mk (ψ s) := by
    intro s
    rw [hΨ, MulEquiv.trans_apply, ← centerQuotientIsogenyEquiv_mk, MulEquiv.symm_apply_apply,
      centerQuotientMulEquiv_mk]
  have hLG := le_pieceSup_of_isScFieldRowFamily hφ
  set f₁ : adjointGroup .E6 (fixSubfield σ) →* pieceSup e ⧸ center (pieceSup e) :=
    Ψ.toMonoidHom.comp (fixedFieldInclusion σ) with hf₁
  set f₂ : adjointGroup .E6 (fixSubfield σ) →* pieceSup e ⧸ center (pieceSup e) :=
    (QuotientGroup.mk' (center (pieceSup e))).comp
      ((L.subtype.comp e.symm.toMonoidHom).codRestrict (pieceSup e) fun x => hLG (e.symm x).2)
    with hf₂
  have hcard : ∀ i : Fin (Tag.rank .E6), ({i} : Finset (Fin (Tag.rank .E6))).card ≤ 2 :=
    fun i => by simp
  have key : ∀ (i : Fin (Tag.rank .E6)) (x : adjointGroup .E6 (fixSubfield σ)),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup {i} →
      f₁ x = f₂ x := by
    intro i x hx
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype hx
    obtain ⟨y', rfl⟩ := leviIsogeny_surjective (K := K) {i} y
    have h1 : fixedFieldInclusion σ x = e6Isogeny K y' := Subtype.ext (by
      rw [coe_fixedFieldInclusion, ← hy, coe_leviIsogeny])
    have h2 := hfix ⟨{i}, hcard i⟩ x hx y' hy
    change Ψ (fixedFieldInclusion σ x) = QuotientGroup.mk _
    rw [h1, hΨθ]
    congr 1
    exact Subtype.ext h2
  have hf : f₁ = f₂ := CFSG.LieType.Ree.adjointGroup_hom_ext
    (fun i c => key i _ (xElement_mem_levi_adjDatumE6 i c))
    (fun i c => key i _ (yElement_mem_levi_adjDatumE6 i c))
  refine ⟨Ψ, fun x g hg => ?_⟩
  have h := DFunLike.congr_fun hf x
  have hg' : ((L.subtype.comp e.symm.toMonoidHom).codRestrict (pieceSup e)
      fun x => hLG (e.symm x).2) x = g := Subtype.ext hg.symm
  change Ψ (fixedFieldInclusion σ x) = _ at h
  rw [h, hf₂, MonoidHom.comp_apply, hg']
  rfl

end Main

end CFSG.SeitzReduction.E6Pilot
