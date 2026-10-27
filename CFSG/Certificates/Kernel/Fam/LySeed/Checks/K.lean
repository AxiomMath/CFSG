module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.LySeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamLySeed

theorem consts : CFSG.KC.Ord.constsOK 5 12 1332 111 8 L H CM RM ONE LV HV = true := by quickRfl

theorem nreg : Nat.beq RWn 19 = true := by quickRfl

end CFSG.KD.FamLySeed

end
