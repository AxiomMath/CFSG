module

public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG

theorem subgroup_solvable_of_solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (H : Subgroup G) : Group.IsSolvable H := by
  infer_instance

end CFSG
