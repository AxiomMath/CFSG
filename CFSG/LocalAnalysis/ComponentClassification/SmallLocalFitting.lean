module

public import CFSG.GroupTheory.LocalCores.FittingNormal
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup CFSG.LocalCores

variable {G : Type*} [Group G]

theorem fittingSubgroup_map_mulEquiv {G' : Type*} [Group G'] (f : G ≃* G') :
    (fittingSubgroup G).map f.toMonoidHom = fittingSubgroup G' :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv f

theorem fitting_subnormal_intersection [Finite G] {N : Subgroup G} (hN : N.IsSubnormal) :
    (fittingSubgroup N).map N.subtype = N ⊓ fittingSubgroup G := by
  induction hN with
  | top =>
    rw [top_inf_eq, ← fittingSubgroup_map_mulEquiv (Subgroup.topEquiv (G := G))]
    rfl
  | step H K hHK _ hHn ih =>
    have := hHn
    have key := fitting_normal_intersection (H.subgroupOf K)
    have hmap := congrArg (Subgroup.map K.subtype) key
    rw [Subgroup.map_inf_eq _ _ _ K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hHK, ih, ← inf_assoc, inf_eq_left.mpr hHK, Subgroup.map_map] at hmap
    rw [← hmap, ← fittingSubgroup_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK),
      Subgroup.map_map]
    rfl

end CFSG.ComponentClassification.SmallLocal
