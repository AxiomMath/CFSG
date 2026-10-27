module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.J4.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamJ4

theorem consts : CFSG.KC.Ord.constsOK 2 8 896 112 5 L H CM RM ONE LV HV = true := by quickRfl

theorem nreg : Nat.beq RWn 239 = true := by quickRfl

end CFSG.KD.FamJ4

end
