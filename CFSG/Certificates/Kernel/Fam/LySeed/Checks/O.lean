module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.LySeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamLySeed

theorem o_A : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 12 1332 111 8 L H CM RM) ONE RWn 1 2 [2] =
    true := by
  quickRfl

theorem o_B : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 12 1332 111 8 L H CM RM) ONE RWn 2 5 [5] =
    true := by
  quickRfl

theorem o_AB : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 12 1332 111 8 L H CM RM) ONE RWn 5 14
    [2, 7] = true := by
  quickRfl

theorem o_x : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 12 1332 111 8 L H CM RM) ONE RWn 18 67
    [67] = true := by
  quickRfl

end CFSG.KD.FamLySeed

end
