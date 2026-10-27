module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGA8Std
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKKGHolds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

section Main



theorem asc82CoreKGAHard_holds (hS : Asc82SchurU43) : Asc82CoreKGAHard :=
  asc82CoreKGAHard_of_fj53 hS asc82CoreKGAHardD4_holds
    (fun _ hs => fkFj53 fa8_std_nondegenerate hs)

end Main

end CFSG.OddStandard.SmallF3.Omega
