module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHN

theorem consts : CFSG.KC.Ord.constsOK (nat_lit 5) (nat_lit 13) (nat_lit 0x6c1) (nat_lit 0x85)
    (nat_lit 9) L H CM RM ONE LV HV = true := by
  quickRfl

end CFSG.KD.OrdHN

end
