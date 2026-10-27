module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.J4.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamJ4

theorem conjA : CFSG.KC.Fam.conjOK (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM)
    (CFSG.KC.Ord.validM 2 100352 L H) ONE Cm Ci (RW 1) (RW 206) = true := by
  quickRfl

theorem conjB : CFSG.KC.Fam.conjOK (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM)
    (CFSG.KC.Ord.validM 2 100352 L H) ONE Cm Ci (RW 2) (RW 238) = true := by
  quickRfl

theorem conjR : CFSG.KC.Ord.andB (CFSG.KC.Ord.regBelow 206 RWn) (CFSG.KC.Ord.regBelow 238 RWn) =
    true := by
  quickRfl

end CFSG.KD.FamJ4

end
