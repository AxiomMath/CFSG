module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutSetup

public section

namespace CFSG.EvenSporadicStandard.M22Std

variable {G : Type} [Group G] {L : Subgroup G} {z : G} {F L1 N : Subgroup G}

namespace OutSetup

variable (S : OutSetup L z F L1 N)

include S

theorem isPGroup_L1 : IsPGroup 2 L1 :=
  IsPGroup.of_card (n := 8) (S.L1_card.trans (by norm_num))

end OutSetup

end CFSG.EvenSporadicStandard.M22Std
