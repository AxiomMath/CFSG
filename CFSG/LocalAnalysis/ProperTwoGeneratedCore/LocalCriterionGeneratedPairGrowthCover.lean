module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOddCore

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] [Finite G]

theorem generatedPairGrowth_odd_core_eq_intersection_of_full_cover
    (E : Subgroup G) (hcover : CFSG.oddCore G ⊔ E = ⊤) :
    (CFSG.oddCore E).map E.subtype = CFSG.oddCore G ⊓ E := by
  apply le_antisymm
  · exact le_inf (odd_core_image_le_of_full_odd_core_cover E hcover)
      (Subgroup.map_subtype_le _)
  · rw [← Subgroup.subgroupOf_map_subtype]
    apply Subgroup.map_mono
    apply CFSG.ComponentClassification.OddCore.maximal
    · infer_instance
    · rw [← Subgroup.card_subtype E ((CFSG.oddCore G).subgroupOf E),
        Subgroup.subgroupOf_map_subtype]
      exact (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
        (Subgroup.card_dvd_of_le inf_le_left)

theorem generatedPairGrowth_ambient_odd_core_eq_intersection_of_full_cover
    (B E : Subgroup G) (hEB : E ≤ B)
    (hcover : (CFSG.oddCore B).map B.subtype ⊔ E = B) :
    (CFSG.oddCore E).map E.subtype = (CFSG.oddCore B).map B.subtype ⊓ E := by
  let EB := E.subgroupOf B
  let e : EB ≃* E := Subgroup.subgroupOfEquivOfLe hEB
  have hcoverB : CFSG.oddCore B ⊔ EB = ⊤ := by
    apply top_unique
    intro b _
    have hm : (CFSG.oddCore B ⊔ EB).map B.subtype = B := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEB]
      exact hcover
    have hmem : (b : G) ∈ (CFSG.oddCore B ⊔ EB).map B.subtype := by
      rw [hm]
      exact b.property
    exact (Subgroup.mem_map_iff_mem B.subtype_injective).mp hmem
  have hcore := generatedPairGrowth_odd_core_eq_intersection_of_full_cover EB hcoverB
  have hmap : (CFSG.oddCore EB).map e.toMonoidHom = CFSG.oddCore E :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcomp : B.subtype.comp EB.subtype = E.subtype.comp e.toMonoidHom := by
    ext a
    rfl
  have hambient := congrArg (Subgroup.map B.subtype) hcore
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hmap,
    Subgroup.map_inf _ _ _ B.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hEB] at hambient
  exact hambient

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
