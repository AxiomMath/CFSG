module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.Fam.LyAlg.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamLyAlg

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

theorem tpose1 : CFSG.KC.Fam.tposeOK (CFSG.KC.Ord.validM 5 147852 L H) 12 1332 111 (RW 1) (RW 3) =
    true := by
  quickRfl

theorem tpose2 : CFSG.KC.Fam.tposeOK (CFSG.KC.Ord.validM 5 147852 L H) 12 1332 111 (RW 2) (RW 4) =
    true := by
  quickRfl

end CFSG.KD.FamLyAlg

end
