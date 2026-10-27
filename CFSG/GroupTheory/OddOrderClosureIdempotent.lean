module

public import CFSG.GroupTheory.OddOrderClosure

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem oddOrderClosure_oddOrderClosure (H : Subgroup G) :
    oddOrderClosure (oddOrderClosure H) = oddOrderClosure H := by
  refine le_antisymm (oddOrderClosure_le _) ?_
  refine (oddOrderClosure_le_iff (H := H)
    (K := oddOrderClosure (oddOrderClosure H))).mpr ?_
  intro g hg
  exact mem_oddOrderClosure_of_mem_of_odd
    (mem_oddOrderClosure_of_mem_of_odd hg.1 hg.2) hg.2

end CFSG.GroupTheory
