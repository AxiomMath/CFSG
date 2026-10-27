module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5LADefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5LACover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Sec5LemmaA_of (hS : Asc82SchurU43) : Asc82Sec5LemmaA := by
  intro h36 G _ _ t L S z hctx w hwt hwz hw6
  exact sec5la_centralizes_of_mem_normalizer hS hctx.toSec5Setting.isOm6Z2 hctx.pocket
    (sec4_mem_normalizer h36 hctx.toSec5Setting.toSec3SettingLB w hwt) hwz hw6

end CFSG.OddStandard.SmallF3.Omega
