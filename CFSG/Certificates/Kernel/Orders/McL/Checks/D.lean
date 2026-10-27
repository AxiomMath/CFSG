module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.McL.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdMcL

theorem d1_0 :
    Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0x1e3 3 0x15 8 0xa8 RM (RW 1) [0, 1] 1) 0x6e7 = true := by
  quickRfl

theorem d1_end :
    CFSG.KC.Ord.seedDone 0x15 (CFSG.KC.Ord.validM 3 0xdc8 L H) (RW 1) 0x6e7 = true := by
  quickRfl

theorem d2_0 :
    Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0x1e3 3 0x15 8 0xa8 RM (RW 2) [0, 1] 1) 0x6e7 = true := by
  quickRfl

theorem d2_end :
    CFSG.KC.Ord.seedDone 0x15 (CFSG.KC.Ord.validM 3 0xdc8 L H) (RW 2) 0x6e7 = true := by
  quickRfl

end CFSG.KD.OrdMcL

end
