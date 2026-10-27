module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Fi22.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdFi22

theorem consts : CFSG.KC.Ord.constsOK 3 0xa 0x302 0x4d 7 L H CM RM ONE LV HV = true := by quickRfl

end CFSG.KD.OrdFi22

end
