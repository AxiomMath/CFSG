module

public import CFSG.CharacterTheory.Wreathed.NormalOddIndexFullCenterLayer
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterLinear

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open NormalOddIndexFullCenterLayer

universe u v

variable {H : Type u} {J : Type v} [Group H] [Group J]

theorem injective_center_image (i : J →* H) (hi : Function.Injective i)
    (M : Subgroup H) (hM : M ≤ i.range) (hA : Subgroup.center H ≤ i.range)
    (hc : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    (Subgroup.center J).map i = Subgroup.center H := by
  let e := MonoidHom.ofInjective hi
  calc
    (Subgroup.center J).map i =
        ((Subgroup.center J).map e.toMonoidHom).map i.range.subtype := by
      rw [Subgroup.map_map]
      rfl
    _ = (Subgroup.center i.range).map i.range.subtype := by
      have he : (Subgroup.center J).map e.toMonoidHom = Subgroup.center i.range :=
        Subgroup.map_center_eq e
      rw [he]
    _ = Subgroup.center H := center_map_eq M i.range hM hA hc

@[expose] def injectiveFullCenterMap (i : J →* H)
    (hcenter : (Subgroup.center J).map i = Subgroup.center H) :
    J ⧸ Subgroup.center J →* H ⧸ Subgroup.center H :=
  QuotientGroup.map _ _ i (Subgroup.map_le_iff_le_comap.mp hcenter.le)

theorem injectiveFullCenterMap_mk (i : J →* H)
    (hcenter : (Subgroup.center J).map i = Subgroup.center H) (j : J) :
    injectiveFullCenterMap i hcenter (QuotientGroup.mk' (Subgroup.center J) j) =
      QuotientGroup.mk' (Subgroup.center H) (i j) := rfl

@[expose] def injectiveRangeFullCenterEquiv (i : J →* H) (hi : Function.Injective i) :
    J ⧸ Subgroup.center J ≃* i.range ⧸ Subgroup.center i.range :=
  QuotientGroup.congr _ _ (MonoidHom.ofInjective hi)
    (Subgroup.map_center_eq (MonoidHom.ofInjective hi))

theorem injectiveRangeFullCenterEquiv_mk (i : J →* H) (hi : Function.Injective i) (j : J) :
    injectiveRangeFullCenterEquiv i hi (QuotientGroup.mk' (Subgroup.center J) j) =
      QuotientGroup.mk' (Subgroup.center i.range) (MonoidHom.ofInjective hi j) := rfl

theorem injectiveFullCenterMap_eq (i : J →* H) (hi : Function.Injective i)
    (M : Subgroup H) (hM : M ≤ i.range)
    (hc : Subgroup.centralizer (M : Set H) = Subgroup.center H)
    (hcenter : (Subgroup.center J).map i = Subgroup.center H) :
    injectiveFullCenterMap i hcenter =
      (fullCenterInclusion M i.range hM hc).comp
        (injectiveRangeFullCenterEquiv i hi).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) a
  rw [injectiveFullCenterMap_mk, MonoidHom.comp_apply]
  change QuotientGroup.mk' (Subgroup.center H) (i j) =
    fullCenterInclusion M i.range hM hc
      (injectiveRangeFullCenterEquiv i hi (QuotientGroup.mk' (Subgroup.center J) j))
  rw [injectiveRangeFullCenterEquiv_mk, fullCenterInclusion_mk]
  rfl


theorem injective_normal_odd_index_full_center_layer [Finite H]
    (i : J →* H) (hi : Function.Injective i) (hnormal : i.range.Normal)
    (hodd : Odd i.range.index) (M : Subgroup H) [M.Normal]
    (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (htwo : IsPGroup 2 (Subgroup.center H))
    (hc : Subgroup.centralizer (M : Set H) = Subgroup.center H) :
    (Subgroup.center J).map i = Subgroup.center H ∧
      ∃ hcenter : (Subgroup.center J).map i = Subgroup.center H,
        let j := injectiveFullCenterMap i hcenter
        Function.Injective j ∧ j.range.Normal ∧ Odd j.range.index ∧
        (∀ a : J, j (QuotientGroup.mk' (Subgroup.center J) a) =
          QuotientGroup.mk' (Subgroup.center H) (i a)) ∧
        (CFSG.generalizedFitting (J ⧸ Subgroup.center J)).map j =
          CFSG.generalizedFitting (H ⧸ Subgroup.center H) ∧
        (∃ E : CFSG.generalizedFitting (J ⧸ Subgroup.center J) ≃*
          CFSG.generalizedFitting (H ⧸ Subgroup.center H),
          ∀ a : CFSG.generalizedFitting (J ⧸ Subgroup.center J),
            (E a : H ⧸ Subgroup.center H) = j (a : J ⧸ Subgroup.center J)) ∧
        IsSimpleGroup (CFSG.generalizedFitting (J ⧸ Subgroup.center J)) ∧
        (∃ a b : CFSG.generalizedFitting (J ⧸ Subgroup.center J), a * b ≠ b * a) ∧
        Subgroup.centralizer (CFSG.generalizedFitting (J ⧸ Subgroup.center J) :
          Set (J ⧸ Subgroup.center J)) = ⊥ := by
  let : Finite J := Finite.of_injective i hi
  let : i.range.Normal := hnormal
  have hMD := quasisimple_le_normal_of_odd_index M i.range hM heven hodd
  have hAD := center_le_normal_of_odd_index i.range htwo hodd
  have hcenter := injective_center_image i hi M hMD hAD hc
  let j := injectiveFullCenterMap i hcenter
  let e := injectiveRangeFullCenterEquiv i hi
  let k := fullCenterInclusion M i.range hMD hc
  have hj : j = k.comp e.toMonoidHom := injectiveFullCenterMap_eq i hi M hMD hc hcenter
  have hk : Function.Injective k := fullCenterInclusion_injective M i.range hMD hc
  have hinj : Function.Injective j := by
    rw [hj]
    exact hk.comp e.injective
  have hrange : j.range = k.range := by
    have he : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
    rw [hj, MonoidHom.range_comp, he, Subgroup.map_top]
  have hnormalj : j.range.Normal := by
    rw [hrange, fullCenterInclusion_range]
    infer_instance
  have hoddj : Odd j.range.index := by
    rw [hrange, fullCenterInclusion_range]
    exact hodd.of_dvd_nat (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))
  let Q := M.map (QuotientGroup.mk' (Subgroup.center H))
  have hQ := projectiveImage_simple M hM hc
  let : IsSimpleGroup Q := hQ.1
  let P := CFSG.generalizedFitting (H ⧸ Subgroup.center H)
  have hP : P = Q := ambient_generalizedFitting M hM hc
  let : IsSimpleGroup P := hP.symm ▸ hQ.1
  have hnonabP : ∃ a b : P, a * b ≠ b * a := by
    exact hP.symm ▸ hQ.2
  let E := layerInclusionEquiv M i.range hM hMD hc
  let : IsSimpleGroup (CFSG.generalizedFitting (i.range ⧸ Subgroup.center i.range)) :=
    E.isSimpleGroup
  have hnonabRange : ∃ a b : CFSG.generalizedFitting
      (i.range ⧸ Subgroup.center i.range), a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.nonabelian_of_equiv E hnonabP
  have hCRange := local_layer_centralizer M i.range hM hMD hc
  let E₀ := DegreeThreeModelFullCenter.generalizedFittingSimpleEquiv
    e.symm hnonabRange hCRange
  let E₁ := E₀.symm.trans E
  let : IsSimpleGroup (CFSG.generalizedFitting (J ⧸ Subgroup.center J)) :=
    E₁.isSimpleGroup
  have hcoe (a : CFSG.generalizedFitting (J ⧸ Subgroup.center J)) :
      (E₁ a : H ⧸ Subgroup.center H) = j (a : J ⧸ Subgroup.center J) := by
    have hpre : (E₀.symm a : i.range ⧸ Subgroup.center i.range) =
        e (a : J ⧸ Subgroup.center J) := by
      apply e.symm.injective
      have hE₀ (b : CFSG.generalizedFitting (i.range ⧸ Subgroup.center i.range)) :
          (E₀ b : J ⧸ Subgroup.center J) = e.symm (b : _) := rfl
      rw [← hE₀, E₀.apply_symm_apply, e.symm_apply_apply]
    change (E (E₀.symm a) : H ⧸ Subgroup.center H) = _
    rw [layerInclusionEquiv_coe, hpre, hj]
    rfl
  have hmap : (CFSG.generalizedFitting (J ⧸ Subgroup.center J)).map j = P := by
    ext h
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hcoe (⟨a, ha⟩ : CFSG.generalizedFitting (J ⧸ Subgroup.center J)) ▸
        (E₁ ⟨a, ha⟩).property
    · intro hh
      obtain ⟨a, ha⟩ := E₁.surjective ⟨h, hh⟩
      exact ⟨a, a.property, (hcoe a).symm.trans (congrArg Subtype.val ha)⟩
  have hnonabJ : ∃ a b : CFSG.generalizedFitting (J ⧸ Subgroup.center J),
      a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.nonabelian_of_equiv E₁ hnonabP
  have hcJ : Subgroup.centralizer (CFSG.generalizedFitting (J ⧸ Subgroup.center J) :
      Set (J ⧸ Subgroup.center J)) = ⊥ := by
    apply centralizer_eq_bot_of_injective j hinj
    rw [hmap]
    exact ambient_layer_centralizer M hM hc
  exact ⟨hcenter, hcenter, hinj, hnormalj, hoddj, injectiveFullCenterMap_mk i hcenter,
    hmap, ⟨E₁, hcoe⟩, inferInstance, hnonabJ, hcJ⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
