module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Co3.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdCo3

theorem d1_0 : Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0x20f 2 0x16 6 0x84 RM (RW 1) [0, 1, 2] 1)
    0x793 = true := by
  quickRfl

theorem d1_end :
    CFSG.KC.Ord.seedDone 0x16 (CFSG.KC.Ord.validM 2 0xb58 L H) (RW 1) 0x793 = true := by
  quickRfl

theorem d2_0 : Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0x20f 2 0x16 6 0x84 RM (RW 2) [0, 1, 2] 1)
    0x793 = true := by
  quickRfl

theorem d2_end :
    CFSG.KC.Ord.seedDone 0x16 (CFSG.KC.Ord.validM 2 0xb58 L H) (RW 2) 0x793 = true := by
  quickRfl

end CFSG.KD.OrdCo3

end
