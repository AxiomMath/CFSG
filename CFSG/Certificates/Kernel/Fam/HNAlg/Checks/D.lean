module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.Fam.HNAlg.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamHNAlg

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

theorem tpose1 : CFSG.KC.Fam.tposeOK (CFSG.KC.Ord.validM 5 229957 L H) 13 1729 133 (RW 1) (RW 3) =
    true := by
  quickRfl

theorem tpose2 : CFSG.KC.Fam.tposeOK (CFSG.KC.Ord.validM 5 229957 L H) 13 1729 133 (RW 2) (RW 4) =
    true := by
  quickRfl

end CFSG.KD.FamHNAlg

end
