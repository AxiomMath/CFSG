module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.He.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdHe

theorem d1_0 : Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0xa0b 7 0x32 0xc 0x258 RM (RW 1)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 1) 0x2713 = true := by
  quickRfl

theorem d1_end :
    CFSG.KC.Ord.seedDone 0x32 (CFSG.KC.Ord.validM 7 0x7530 L H) (RW 1) 0x2713 = true := by
  quickRfl

theorem d2_0 : Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0xa0b 7 0x32 0xc 0x258 RM (RW 2)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 1) 0x2713 = true := by
  quickRfl

theorem d2_end :
    CFSG.KC.Ord.seedDone 0x32 (CFSG.KC.Ord.validM 7 0x7530 L H) (RW 2) 0x2713 = true := by
  quickRfl

end CFSG.KD.OrdHe

end
