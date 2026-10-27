module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamHNSeed

theorem o_A : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM) ONE RWn 1 2 [2] =
    true := by
  quickRfl

theorem o_B : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM) ONE RWn 2 3 [3] =
    true := by
  quickRfl

theorem o_AB : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM) ONE RWn 5 22
    [2, 11] = true := by
  quickRfl

theorem o_X : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM) ONE RWn 20 19
    [19] = true := by
  quickRfl

end CFSG.KD.FamHNSeed

end
