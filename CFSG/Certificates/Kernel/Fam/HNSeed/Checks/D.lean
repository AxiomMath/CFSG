module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamHNSeed

theorem d1 : Nat.beq (CFSG.KC.Ord.decRun P1 256 17976 5 133 13 1729 RM (RW 1) (List.range 71) 1)
    70759 = true := by
  quickRfl

theorem d1_end : CFSG.KC.Ord.seedDone 133 (CFSG.KC.Ord.validM 5 229957 L H) (RW 1) 70759 = true := by
  quickRfl

theorem d2 : Nat.beq (CFSG.KC.Ord.decRun P2 256 17976 5 133 13 1729 RM (RW 2) (List.range 71) 1)
    70759 = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone 133 (CFSG.KC.Ord.validM 5 229957 L H) (RW 2) 70759 = true := by
  quickRfl

end CFSG.KD.FamHNSeed

end
