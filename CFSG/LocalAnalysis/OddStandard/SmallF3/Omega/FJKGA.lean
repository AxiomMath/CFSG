module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXHard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Scope
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGD4Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAO5
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAO7
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint


theorem asc82CoreKGAHard_of_d4 (hS : Asc82SchurU43) (hD4 : Asc82CoreKGAHardD4)
    (hM : ∀ (Y : Type) [Group Y], LieModel Y .POmegaMinus 4 3 1 → FJKGAAt Y) :
    Asc82CoreKGAHard := by
  intro Y _ _ hY hC
  rcases l34g_hard_scope hY hC with (h | h | h | h | h | h) | ⟨hq, h⟩
  · exact fjKGAAt_of_lieModel_psp h
  · exact fjKGAAt_of_lieModel_psl h
  · exact fjKGAAt_of_lieModel_psu h
  · exact fjKGAAt_of_lieModel_odd h
  · exact hD4 Y h hC
  · exact hM Y h
  · exact fjKGAAt_of_isTwoU43 hS hq h

end CFSG.OddStandard.SmallF3.Omega
