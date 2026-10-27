module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HS.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHS

theorem consts : CFSG.KC.Ord.constsOK 2 6 0x78 0x14 4 L H CM RM ONE LV HV = true := by quickRfl

end CFSG.KD.OrdHS

end
