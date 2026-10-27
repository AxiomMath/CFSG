module

public import CFSG.Certificates.Kernel.Orders.Cert
public import CFSG.Certificates.Kernel.Orders.Fi22.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.OrdFi22

theorem d1_0 : Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0x178b 3 0x4d 0xa 0x302 RM (RW 1)
    (List.range' 0 16) 1) 0x3edf = true := by
  quickRfl

theorem d1_16 : Nat.beq (CFSG.KC.Ord.decRun P1 0x100 0x178b 3 0x4d 0xa 0x302 RM (RW 1)
    (List.range' 16 8) 0x3edf) 0x5ca7 = true := by
  quickRfl

theorem d1_end :
    CFSG.KC.Ord.seedDone 0x4d (CFSG.KC.Ord.validM 3 0xe79a L H) (RW 1) 0x5ca7 = true := by
  quickRfl

theorem d2_0 : Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0x178b 3 0x4d 0xa 0x302 RM (RW 2)
    (List.range' 0 16) 1) 0x3edf = true := by
  quickRfl

theorem d2_16 : Nat.beq (CFSG.KC.Ord.decRun P2 0x100 0x178b 3 0x4d 0xa 0x302 RM (RW 2)
    (List.range' 16 8) 0x3edf) 0x5ca7 = true := by
  quickRfl

theorem d2_end :
    CFSG.KC.Ord.seedDone 0x4d (CFSG.KC.Ord.validM 3 0xe79a L H) (RW 2) 0x5ca7 = true := by
  quickRfl

end CFSG.KD.OrdFi22

end
