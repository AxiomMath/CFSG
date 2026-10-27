module

public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.GroupTheory

variable {A : Type*} [Group A]

theorem map_center_subgroupOf_eq_subgroupOf_map_center (Y S : Subgroup A) (hSY : S ≤ Y) :
    (Subgroup.center (S.subgroupOf Y)).map (S.subgroupOf Y).subtype =
      ((Subgroup.center S).map S.subtype).subgroupOf Y := by
  have hWY : (Subgroup.center S).map S.subtype ≤ Y :=
    (Subgroup.map_subtype_le (H := S) (K := Subgroup.center S)).trans hSY
  have hcomp : Y.subtype.comp (S.subgroupOf Y).subtype =
      S.subtype.comp (Subgroup.subgroupOfEquivOfLe hSY : ↥(S.subgroupOf Y) →* ↥S) := by
    ext g
    exact (Subgroup.subgroupOfEquivOfLe_apply_coe hSY g).symm
  apply Subgroup.map_injective (f := Y.subtype) Y.subtype_injective
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hSY),
    Subgroup.map_subgroupOf_eq_of_le hWY]

end CFSG.GroupTheory
