module

import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

theorem card_eq_of_statedClassicalModel_psu_three_three {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

end CFSG.LinearGroups.UnitaryThreeOverNine
