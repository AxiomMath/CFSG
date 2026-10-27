module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.J3.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdJ3

theorem consts : CFSG.KC.Ord.constsOK 2 8 0x280 0x50 6 L H CM RM ONE LV HV = true := by quickRfl

end CFSG.KD.OrdJ3

end
