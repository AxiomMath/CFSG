module

public import Mathlib.GroupTheory.GroupAction.ConjAct

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {H K : Subgroup G}

theorem normal_of_characteristic_subgroupOf_of_normal (hHK : H ≤ K) [K.Normal]
    [(H.subgroupOf K).Characteristic] : H.Normal := by
  have h : ((H.subgroupOf K).map K.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  rwa [H.subgroupOf_map_subtype K, inf_eq_left.mpr hHK] at h

theorem characteristic_of_characteristic_subgroupOf_of_characteristic (hHK : H ≤ K)
    [K.Characteristic] [(H.subgroupOf K).Characteristic] : H.Characteristic := by
  have h : ((H.subgroupOf K).map K.subtype).Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
  rwa [H.subgroupOf_map_subtype K, inf_eq_left.mpr hHK] at h

end CFSG.FeitThompson
