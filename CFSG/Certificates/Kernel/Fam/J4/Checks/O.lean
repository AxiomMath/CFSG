module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.J4.Data.Sel
public import CFSG.Certificates.Kernel.J4.KRSData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamJ4

theorem o_A : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 1 2 [2] =
    true := by
  quickRfl

theorem o_B : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 2 4 [2] =
    true := by
  quickRfl

theorem o_AB : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 48 37
    [37] = true := by
  quickRfl

theorem o_rel : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 61 43
    [43] = true := by
  quickRfl

theorem o_x : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 22 2 [2] =
    true := by
  quickRfl

theorem o_y : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 26 3 [3] =
    true := by
  quickRfl

theorem o_t : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 35 2 [2] =
    true := by
  quickRfl

theorem o_z : CFSG.KC.Fam.ordExact RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM) ONE RWn 47 2 [2] =
    true := by
  quickRfl

theorem o_gcd : CFSG.KC.Ord.andB (CFSG.KC.Fam.coprime 2 37)
    (CFSG.KC.Fam.coprime 43 CFSG.KJ4.KRS.BK) = true := by
  quickRfl

end CFSG.KD.FamJ4

end
