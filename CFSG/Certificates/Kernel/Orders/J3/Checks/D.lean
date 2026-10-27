module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.J3.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdJ3

theorem d1_0 : Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0x1965 2 0x50 8 0x280 RM (RW 1)
    (List.range' 0 16) 1) 0x3ee7 = true := by
  quickRfl

theorem d1_16 : Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0x1965 2 0x50 8 0x280 RM (RW 1)
    (List.range' 16 10) 0x3ee7) 0x6403 = true := by
  quickRfl

theorem d1_end :
    CFSG.KC.Ord.seedDone 0x50 (CFSG.KC.Ord.validM 2 0xc800 L H) (RW 1) 0x6403 = true := by
  quickRfl

theorem d2_0 : Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0x1965 2 0x50 8 0x280 RM (RW 2)
    (List.range' 0 16) 1) 0x3ee7 = true := by
  quickRfl

theorem d2_16 : Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0x1965 2 0x50 8 0x280 RM (RW 2)
    (List.range' 16 10) 0x3ee7) 0x6403 = true := by
  quickRfl

theorem d2_end :
    CFSG.KC.Ord.seedDone 0x50 (CFSG.KC.Ord.validM 2 0xc800 L H) (RW 2) 0x6403 = true := by
  quickRfl

end CFSG.KD.OrdJ3

end
