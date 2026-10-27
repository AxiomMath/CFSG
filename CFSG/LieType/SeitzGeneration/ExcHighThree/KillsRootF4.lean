module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootCombF4
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroupF4

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups

section Cycle


theorem killsCycleShape_F4 : KillsCycleShape Tag.F4 :=
  fun χ w hw _ hα => f4_exists_kill_root_cycle rfl χ w hw hα

end Cycle


theorem langPlaneKillsRoot_F4 : LangPlaneKillsRoot Tag.F4 :=
  langPlaneKillsRoot_F4_of_cycle killsCycleShape_F4

end CFSG.LieType.SeitzGeneration.ExcHighThree
