module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.Fam.HNAlg.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamHNAlg

theorem consts : CFSG.KC.Ord.constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true := by quickRfl

theorem nreg : Nat.beq RWn 13 = true := by quickRfl

end CFSG.KD.FamHNAlg

end
