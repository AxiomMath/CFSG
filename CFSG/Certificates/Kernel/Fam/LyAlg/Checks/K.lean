module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.Fam.LyAlg.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamLyAlg

theorem consts : CFSG.KC.Ord.constsOK 5 12 1332 111 8 L H CM RM ONE LV HV = true := by quickRfl

theorem nreg : Nat.beq RWn 13 = true := by quickRfl

end CFSG.KD.FamLyAlg

end
