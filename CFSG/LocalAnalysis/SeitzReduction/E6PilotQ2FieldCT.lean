module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.CurtisTits (IsCompatible)

local instance e6PilotQ2FieldCTNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section CT


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E6 (fixSubfield σ))

structure IsTwoFieldFamilyE6 (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (adjDatumE6 K).leviAmalgam φ
  fix : ∀ J (x : adjointGroup .E6 (fixSubfield σ)),
    x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1 →
    ∀ y : (adjDatumE6 K).leviAmalgam J, ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ)) →
      φ J y = ((e.symm x : L) : G)

variable {e}

@[expose] noncomputable def twoFamilySupE6 (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G) :
    Subgroup G :=
  ⨆ J, (φ J).range

theorem mem_twoFamilySupE6 (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G)
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) (y : (adjDatumE6 K).leviAmalgam J) :
    φ J y ∈ twoFamilySupE6 φ :=
  le_iSup (fun J => (φ J).range) J ⟨y, rfl⟩

variable [Finite K]

theorem exists_surjective_twoFamilySupE6 {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsTwoFieldFamilyE6 e φ) :
    ∃ ψ : e6Data_valid.minGroup K →* twoFamilySupE6 φ,
      Function.Surjective ψ ∧ ψ.ker ≤ center (e6Data_valid.minGroup K) ∧
      center (twoFamilySupE6 φ) = (center (e6Data_valid.minGroup K)).map ψ ∧
      ∀ J (x : adjointGroup .E6 (fixSubfield σ)),
        x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J.1 →
        ∀ y : (e6Datum K).leviAmalgam J, ((e6Isogeny K y : adjointGroup .E6 K) : ModGL .E6 K) =
          baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ)) →
          ((ψ y : twoFamilySupE6 φ) : G) = ((e.symm x : L) : G) := by
  have hcard : ∀ i : Fin (Tag.rank .E6), ({i} : Finset (Fin (Tag.rank .E6))).card ≤ 2 :=
    fun i => by simp
  set G₀ := twoFamilySupE6 φ with hG₀
  set φs := scFamily φ with hφs
  have hle : ∀ J y, φs J y ∈ G₀ := fun J y => mem_twoFamilySupE6 φ J _
  set φ' : ∀ J, (e6Datum K).leviAmalgam J →* G₀ := fun J => (φs J).codRestrict G₀ (hle J)
    with hφ'def
  have hφ' : IsCompatible (e6Datum K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (isCompatible_scFamily hφ.compatible i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    exact range_scFamily φ J
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_levi_adjDatumE6 (k := fixSubfield σ) 0
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype hu
    obtain ⟨y', rfl⟩ := leviIsogeny_surjective (K := K) {0} y
    refine ⟨⟨{0}, hcard 0⟩, y', fun h => hu1 ?_⟩
    have h1 : φs ⟨{0}, hcard 0⟩ y' = 1 := congrArg Subtype.val h
    rw [hφs, scFamily_apply, hφ.fix ⟨{0}, hcard 0⟩ u hu _ hy] at h1
    have h2 : e.symm u = 1 := Subtype.ext h1
    rw [← map_one e.symm] at h2
    exact e.symm.injective h2
  obtain ⟨ψ, hψ, hsurj, hker, -, hZ⟩ := exists_surjective_of_isCompatible_e6 K φ' hφ' hgen' hnt
  refine ⟨ψ, hsurj, hker, hZ, fun J x hx y hxy => ?_⟩
  have h1 : ((ψ y : G₀) : G) = φs J y := congrArg Subtype.val (hψ J y)
  rw [h1, hφs, scFamily_apply]
  exact hφ.fix J x hx _ (by rw [coe_leviIsogeny]; exact hxy)

theorem isQuasisimple_twoFamilySupE6 {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsTwoFieldFamilyE6 e φ) : CFSG.IsQuasisimple (twoFamilySupE6 φ) := by
  obtain ⟨ψ, hsurj, hker, -⟩ := exists_surjective_twoFamilySupE6 hφ
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

theorem commutator_twoFamilySupE6 {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsTwoFieldFamilyE6 e φ) : ⁅twoFamilySupE6 φ, twoFamilySupE6 φ⁆ = twoFamilySupE6 φ :=
  Subgroup.isPerfect_iff.1 (isQuasisimple_twoFamilySupE6 hφ).1

omit [Finite K] in
theorem le_twoFamilySupE6 {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsTwoFieldFamilyE6 e φ) : L ≤ twoFamilySupE6 φ := by
  have hcard : ∀ i : Fin (Tag.rank .E6), ({i} : Finset (Fin (Tag.rank .E6))).card ≤ 2 :=
    fun i => by simp
  have key : ∀ (i : Fin (Tag.rank .E6)) (x : adjointGroup .E6 (fixSubfield σ)),
      x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup {i} →
      ((e.symm x : L) : G) ∈ twoFamilySupE6 φ := by
    intro i x hx
    obtain ⟨y, hy⟩ := exists_levi_adjDatumE6_baseChangeGL (K := K) (fixSubfield σ).subtype hx
    rw [← hφ.fix ⟨{i}, hcard i⟩ x hx y hy]
    exact mem_twoFamilySupE6 φ ⟨{i}, hcard i⟩ y
  have hle : (⊤ : Subgroup (adjointGroup .E6 (fixSubfield σ))) ≤
      (twoFamilySupE6 φ).comap (L.subtype.comp e.symm.toMonoidHom) := by
    rw [← CFSG.LieType.Ree.closure_xElement_yElement, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact key i _ (xElement_mem_levi_adjDatumE6 i c)
    · exact key i _ (yElement_mem_levi_adjDatumE6 i c)
  intro g hg
  have h := hle (mem_top (e ⟨g, hg⟩))
  simpa using h

theorem odd_card_center_twoFamilySupE6 {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G}
    (hφ : IsTwoFieldFamilyE6 e φ) : Odd (Nat.card (center (twoFamilySupE6 φ))) := by
  obtain ⟨ψ, -, -, hZ, -⟩ := exists_surjective_twoFamilySupE6 hφ
  have h1 : Nat.card (center (twoFamilySupE6 φ)) ∣ 3 := by
    rw [hZ]
    refine (Subgroup.card_map_dvd _ ψ).trans ?_
    rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K).1]
    exact Nat.gcd_dvd_left 3 _
  exact Odd.of_dvd_nat (by decide) h1

theorem exists_mulEquiv_center_quotient_twoFamilySupE6
    {φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G} (hφ : IsTwoFieldFamilyE6 e φ) :
    ∃ Ψ : adjointGroup .E6 K ≃* (twoFamilySupE6 φ ⧸ center (twoFamilySupE6 φ)),
      ∀ (x : adjointGroup .E6 (fixSubfield σ)) (g : twoFamilySupE6 φ),
        (g : G) = ((e.symm x : L) : G) → Ψ (fixedFieldInclusion σ x) = QuotientGroup.mk g := by
  obtain ⟨ψ, hsurj, hker, hZ, hfix⟩ := exists_surjective_twoFamilySupE6 hφ
  set Ψ := (centerQuotientIsogenyEquiv (K := K)).symm.trans
    (centerQuotientMulEquiv ψ hsurj hker hZ) with hΨ
  have hΨθ : ∀ s, Ψ (e6Isogeny K s) = QuotientGroup.mk (ψ s) := by
    intro s
    rw [hΨ, MulEquiv.trans_apply, ← centerQuotientIsogenyEquiv_mk, MulEquiv.symm_apply_apply,
      centerQuotientMulEquiv_mk]
  have hLG := le_twoFamilySupE6 hφ
  set f₁ : adjointGroup .E6 (fixSubfield σ) →* twoFamilySupE6 φ ⧸ center (twoFamilySupE6 φ) :=
    Ψ.toMonoidHom.comp (fixedFieldInclusion σ) with hf₁
  set f₂ : adjointGroup .E6 (fixSubfield σ) →* twoFamilySupE6 φ ⧸ center (twoFamilySupE6 φ) :=
    (QuotientGroup.mk' (center (twoFamilySupE6 φ))).comp
      ((L.subtype.comp e.symm.toMonoidHom).codRestrict (twoFamilySupE6 φ)
        fun x => hLG (e.symm x).2) with hf₂
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
  have hg' : ((L.subtype.comp e.symm.toMonoidHom).codRestrict (twoFamilySupE6 φ)
      fun x => hLG (e.symm x).2) x = g := Subtype.ext hg.symm
  change Ψ (fixedFieldInclusion σ x) = _ at h
  rw [h, hf₂, MonoidHom.comp_apply, hg']
  rfl

end CT

end CFSG.SeitzReduction.E6Pilot
