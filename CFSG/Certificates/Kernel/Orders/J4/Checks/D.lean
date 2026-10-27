module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.J4.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdJ4

open CFSG.KC.Ord

theorem d1 : Nat.beq (decRun P1 0x100 0x31f5 2 0x70 8 0x380 RM (RW 1) (List.range 50) 1)
    0xc403 = true := by
  quickRfl

theorem d1_end : seedDone 0x70 (validM 2 0x18800 L H) (RW 1) 0xc403 = true := by quickRfl

theorem d2 : Nat.beq (decRun P2 0x100 0x31f5 2 0x70 8 0x380 RM (RW 2) (List.range 50) 1)
    0xc403 = true := by
  quickRfl

theorem d2_end : seedDone 0x70 (validM 2 0x18800 L H) (RW 2) 0xc403 = true := by quickRfl

end CFSG.KD.OrdJ4

end
