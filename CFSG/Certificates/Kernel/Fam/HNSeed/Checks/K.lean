module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamHNSeed

theorem consts : CFSG.KC.Ord.constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true := by quickRfl

theorem nreg : Nat.beq RWn 21 = true := by quickRfl

end CFSG.KD.FamHNSeed

end
