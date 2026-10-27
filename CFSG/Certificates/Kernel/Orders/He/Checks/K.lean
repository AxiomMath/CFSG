module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.He.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHe

theorem consts : CFSG.KC.Ord.constsOK 7 0xc 0x258 0x32 8 L H CM RM ONE LV HV = true := by quickRfl

end CFSG.KD.OrdHe

end
