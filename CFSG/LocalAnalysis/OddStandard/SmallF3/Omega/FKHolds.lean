module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKAssemble

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

section Main


theorem asc82OmegaPlusAutInvolutions_holds : Asc82OmegaPlusAutInvolutions :=
  asc82OmegaPlusAutInvolutions_of_multNegOne fkMultNegOne_holds

end Main

end CFSG.OddStandard.SmallF3.Omega
