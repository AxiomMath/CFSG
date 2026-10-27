module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldLayerTransport

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open CFSG.Wreathed.NormalOddIndexFullCenterLayer
open scoped Classical

universe u v
variable {H : Type u} {J : Type v} [Group H] [Group J]

theorem full_center_inputs_in_normal_odd_index [Finite H]
    (M D : Subgroup H) [D.Normal] (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (htwo : IsPGroup 2 (Subgroup.center H))
    (hc : Subgroup.centralizer (M : Set H) = Subgroup.center H) (hodd : Odd D.index) :
    M ≤ D ∧ CFSG.IsQuasisimple (M.subgroupOf D) ∧
      Even (Nat.card (M.subgroupOf D ⧸ Subgroup.center (M.subgroupOf D))) ∧
      IsPGroup 2 (Subgroup.center D) ∧
      Subgroup.centralizer (M.subgroupOf D : Set D) = Subgroup.center D := by
  have hMD := quasisimple_le_normal_of_odd_index M D hM heven hodd
  let E := Subgroup.subgroupOfEquivOfLe hMD
  let E0 := QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)
  have hquasi : CFSG.IsQuasisimple (M.subgroupOf D) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv E.symm hM
  have heven0 : Even (Nat.card (M.subgroupOf D ⧸ Subgroup.center (M.subgroupOf D))) := by
    rw [Nat.card_congr E0.toEquiv]
    exact heven
  have htwo0 : IsPGroup 2 (Subgroup.center D) := by
    rw [← center_subgroupOf_eq M D hMD hc]
    exact htwo.comap_subtype
  have hc0 : Subgroup.centralizer (M.subgroupOf D : Set D) = Subgroup.center D := by
    rw [← centralizer_comap_of_injective D.subtype D.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hMD, hc]
    exact center_subgroupOf_eq M D hMD hc
  exact ⟨hMD, hquasi, heven0, htwo0, hc0⟩

theorem nested_normal_odd_index_full_center_layer [Finite H]
    (M D : Subgroup H) [M.Normal] [D.Normal] (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (htwo : IsPGroup 2 (Subgroup.center H))
    (hc : Subgroup.centralizer (M : Set H) = Subgroup.center H) (hodd : Odd D.index)
    (i : J →* D) (hi : Function.Injective i) (hinormal : i.range.Normal)
    (hiodd : Odd i.range.index) :
    (Subgroup.center J).map (D.subtype.comp i) = Subgroup.center H ∧
      ∃ hcenter : (Subgroup.center J).map (D.subtype.comp i) = Subgroup.center H,
        let j := injectiveFullCenterMap (D.subtype.comp i) hcenter
        Function.Injective j ∧
          (∀ a : J, j (QuotientGroup.mk' (Subgroup.center J) a) =
            QuotientGroup.mk' (Subgroup.center H) ((i a : D) : H)) ∧
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
  obtain ⟨hMD, hM0, heven0, htwo0, hc0⟩ :=
    full_center_inputs_in_normal_odd_index M D hM heven htwo hc hodd
  obtain ⟨hcenter0, hcenter0', hj0inj, _, _, hj0mk, hj0map, ⟨E0, hE0⟩,
    hsimple, hnonab, hcentral⟩ :=
    injective_normal_odd_index_full_center_layer i hi hinormal hiodd
      (M.subgroupOf D) hM0 heven0 htwo0 hc0
  have hcenter : (Subgroup.center J).map (D.subtype.comp i) = Subgroup.center H := by
    rw [← Subgroup.map_map, hcenter0]
    exact center_map_eq M D hMD (center_le_normal_of_odd_index D htwo hodd) hc
  let j := injectiveFullCenterMap (D.subtype.comp i) hcenter
  let j0 := injectiveFullCenterMap i hcenter0'
  let k := fullCenterInclusion M D hMD hc
  have hj : j = k.comp j0 := by
    apply MonoidHom.ext
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) a
    change injectiveFullCenterMap (D.subtype.comp i) hcenter
      (QuotientGroup.mk' (Subgroup.center J) b) =
      fullCenterInclusion M D hMD hc
        (injectiveFullCenterMap i hcenter0' (QuotientGroup.mk' (Subgroup.center J) b))
    rw [injectiveFullCenterMap_mk, hj0mk, fullCenterInclusion_mk]
    rfl
  have hinj : Function.Injective j := by
    rw [hj]
    exact (fullCenterInclusion_injective M D hMD hc).comp hj0inj
  have hmap : (CFSG.generalizedFitting (J ⧸ Subgroup.center J)).map j =
      CFSG.generalizedFitting (H ⧸ Subgroup.center H) := by
    rw [hj, ← Subgroup.map_map, hj0map]
    exact generalizedFitting_map M D hM hMD hc
  let E1 := layerInclusionEquiv M D hM hMD hc
  let E := E0.trans E1
  have hvalue (a : CFSG.generalizedFitting (J ⧸ Subgroup.center J)) :
      (E a : H ⧸ Subgroup.center H) = j (a : J ⧸ Subgroup.center J) := by
    change (E1 (E0 a) : H ⧸ Subgroup.center H) = _
    rw [layerInclusionEquiv_coe, hE0, hj]
    rfl
  exact ⟨hcenter, hcenter, hinj, injectiveFullCenterMap_mk _ hcenter,
    hmap, ⟨E, hvalue⟩, hsimple, hnonab, hcentral⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
