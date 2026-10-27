module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdLy

theorem consts : CFSG.KC.Ord.constsOK 5 12 0x534 0x6f 8 L H CM RM ONE LV HV = true := by quickRfl

end CFSG.KD.OrdLy

end
