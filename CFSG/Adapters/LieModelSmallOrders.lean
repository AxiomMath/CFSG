module

public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Blueprint

open Assembly.LowTwoRank

variable {X : Type} [Group X]

theorem LieModel.card_psl_three_four (h : LieModel X .PSL 3 2 2) : Nat.card X = 20160 :=
  Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (h.statedClassicalModel (by decide))

theorem LieModel.card_psu_three_three (h : LieModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  Open.StatedAPI.card_of_statedClassicalModel_psu_three_three (h.statedClassicalModel (by decide))

end CFSG.Blueprint
