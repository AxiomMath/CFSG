module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Ly.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdLy

open CFSG.KC.Ord

theorem d1 : Nat.beq (decRun P1 0x100 0x468f 5 0x6f 12 0x534 RM (RW 1) (List.range 71) 1)
    0xc087 = true := by
  quickRfl

theorem d1_end : seedDone 0x6f (validM 5 0x2418c L H) (RW 1) 0xc087 = true := by quickRfl

theorem d2 : Nat.beq (decRun P2 0x100 0x468f 5 0x6f 12 0x534 RM (RW 2) (List.range 71) 1)
    0xc087 = true := by
  quickRfl

theorem d2_end : seedDone 0x6f (validM 5 0x2418c L H) (RW 2) 0xc087 = true := by quickRfl

end CFSG.KD.OrdLy

end
