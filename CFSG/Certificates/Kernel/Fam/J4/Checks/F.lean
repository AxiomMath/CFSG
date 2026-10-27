module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.J4.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamJ4

theorem fix_x : CFSG.KC.Fam.fixedOK RW (CFSG.KC.Ord.vecR 2 8 896 112 5 LV HV RM)
    (CFSG.KC.Ord.validM 2 896 LV HV) RWn v 22 = true := by
  quickRfl

theorem fix_y : CFSG.KC.Fam.fixedOK RW (CFSG.KC.Ord.vecR 2 8 896 112 5 LV HV RM)
    (CFSG.KC.Ord.validM 2 896 LV HV) RWn v 26 = true := by
  quickRfl

theorem fix_z : CFSG.KC.Fam.fixedOK RW (CFSG.KC.Ord.vecR 2 8 896 112 5 LV HV RM)
    (CFSG.KC.Ord.validM 2 896 LV HV) RWn v 47 = true := by
  quickRfl

theorem kerline : CFSG.KC.Fam.kerLineOK 2 8 5 L H CM ONE (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM)
    (CFSG.KC.Ord.validM 2 100352 L H) (CFSG.KC.Ord.validM 2 896 LV HV) (RW 22) (RW 26) (RW 47) Y1 Y2
    Y3 C0 v = true := by
  quickRfl

end CFSG.KD.FamJ4

end
