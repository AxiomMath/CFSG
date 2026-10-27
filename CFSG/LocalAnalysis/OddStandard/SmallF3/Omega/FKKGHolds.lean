module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKHolds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKKGEight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

section Main


theorem asc82CoreKGAHardD4_holds : Asc82CoreKGAHardD4 :=
  asc82CoreKGAHardD4_of asc82OmegaPlusAutInvolutions_holds

end Main

end CFSG.OddStandard.SmallF3.Omega
