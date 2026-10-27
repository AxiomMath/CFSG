module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] [Finite G]

theorem normal_map_subtype_fittingRaw {N : Subgroup G} (hN : N.Normal) :
    ((fittingRaw N).map N.subtype).Normal :=
  have : N.Normal := hN
  ConjAct.normal_of_characteristic_of_normal

theorem isNilpotent_map_subtype_fittingRaw (N : Subgroup G) :
    Group.IsNilpotent ((fittingRaw N).map N.subtype) :=
  Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective (fittingRaw N) N.subtype N.subtype_injective)

theorem map_subtype_fittingRaw_le_fittingRaw {N : Subgroup G} (hN : N.Normal) :
    (fittingRaw N).map N.subtype ≤ fittingRaw G :=
  le_fittingRaw_of_normal_of_isNilpotent (normal_map_subtype_fittingRaw hN)
    (isNilpotent_map_subtype_fittingRaw N)

theorem fittingRaw_le_subgroupOf_fittingRaw {N : Subgroup G} (hN : N.Normal) :
    fittingRaw N ≤ (fittingRaw G).subgroupOf N := fun _ hx =>
  map_subtype_fittingRaw_le_fittingRaw hN ⟨_, hx, rfl⟩

theorem subgroupOf_fittingRaw_le_fittingRaw (N : Subgroup G) :
    (fittingRaw G).subgroupOf N ≤ fittingRaw N := by
  have hnorm : ((fittingRaw G).subgroupOf N).Normal := inferInstance
  have hnil : Group.IsNilpotent ((fittingRaw G).subgroupOf N) := by
    have h : Group.IsNilpotent (((fittingRaw G).subgroupOf N).map N.subtype) := by
      apply isNilpotent_of_le_fittingRaw
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_le_left
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).symm
  exact le_fittingRaw_of_normal_of_isNilpotent hnorm hnil

theorem fittingRaw_eq_subgroupOf_fittingRaw {N : Subgroup G} (hN : N.Normal) :
    fittingRaw N = (fittingRaw G).subgroupOf N :=
  le_antisymm (fittingRaw_le_subgroupOf_fittingRaw hN) (subgroupOf_fittingRaw_le_fittingRaw N)

theorem map_subtype_fittingRaw_eq_inf {N : Subgroup G} (hN : N.Normal) :
    (fittingRaw N).map N.subtype = fittingRaw G ⊓ N := by
  rw [fittingRaw_eq_subgroupOf_fittingRaw hN, Subgroup.subgroupOf_map_subtype]

theorem fittingRaw_eq_top_of_le_fittingRaw {N : Subgroup G} (hN : N.Normal)
    (h : N ≤ fittingRaw G) : fittingRaw N = ⊤ := by
  rw [fittingRaw_eq_subgroupOf_fittingRaw hN, Subgroup.subgroupOf_eq_top]
  exact h

end

end CFSG.FeitThompson
