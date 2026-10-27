module

public import Mathlib.GroupTheory.Index

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X]

theorem relIndex_map_eq_of_ker_le (α : H →* X) {T N : Subgroup H} (hker : α.ker ≤ T)
    (hTN : T ≤ N) : (T.map α).relIndex (N.map α) = T.relIndex N := by
  rw [Subgroup.relIndex_map_map, sup_eq_left.mpr hker, sup_eq_left.mpr (hker.trans hTN)]

end CFSG.OddStandard.SmallF3.Omega
