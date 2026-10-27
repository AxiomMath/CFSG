module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.LySeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamLySeed

theorem d1 : Nat.beq (CFSG.KC.Ord.decRun P1 256 18063 5 111 12 1332 RM (RW 1) (List.range 71) 1)
    49287 = true := by
  quickRfl

theorem d1_end : CFSG.KC.Ord.seedDone 111 (CFSG.KC.Ord.validM 5 147852 L H) (RW 1) 49287 = true := by
  quickRfl

theorem d2 : Nat.beq (CFSG.KC.Ord.decRun P2 256 18063 5 111 12 1332 RM (RW 2) (List.range 71) 1)
    49287 = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone 111 (CFSG.KC.Ord.validM 5 147852 L H) (RW 2) 49287 = true := by
  quickRfl

end CFSG.KD.FamLySeed

end
