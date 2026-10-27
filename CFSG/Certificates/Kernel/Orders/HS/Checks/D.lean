module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.HS.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHS

theorem d1_0 :
    Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0x1b9 2 0x14 6 0x78 RM (RW 1) [0, 1] 1) 0x643 = true := by
  quickRfl

theorem d1_end :
    CFSG.KC.Ord.seedDone 0x14 (CFSG.KC.Ord.validM 2 0x960 L H) (RW 1) 0x643 = true := by
  quickRfl

theorem d2_0 :
    Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0x1b9 2 0x14 6 0x78 RM (RW 2) [0, 1] 1) 0x643 = true := by
  quickRfl

theorem d2_end :
    CFSG.KC.Ord.seedDone 0x14 (CFSG.KC.Ord.validM 2 0x960 L H) (RW 2) 0x643 = true := by
  quickRfl

end CFSG.KD.OrdHS

end
