module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.McL.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdMcL

theorem consts : CFSG.KC.Ord.constsOK 3 8 0xa8 0x15 5 L H CM RM ONE LV HV = true := by quickRfl

end CFSG.KD.OrdMcL

end
