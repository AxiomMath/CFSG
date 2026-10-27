module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.Fam.HNAlg.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamHNAlg

theorem treec : CFSG.KC.Fam.treeVecOK Vc (CFSG.KC.Ord.vecR 5 13 1729 133 9 LV HV RM) (RW 3) (RW 4)
    vrow PTc 133 = true := by
  quickRfl

theorem basisc : CFSG.KC.Fam.rowsBasis Vc (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM)
    (CFSG.KC.Ord.validM 5 229957 L H) (CFSG.KC.Ord.validM 5 1729 LV HV) 1729 133 ONE Mic = true := by
  quickRfl

theorem treer : CFSG.KC.Fam.treeVecOK Vr (CFSG.KC.Ord.vecR 5 13 1729 133 9 LV HV RM) (RW 1) (RW 2)
    urow PTr 133 = true := by
  quickRfl

theorem basisr : CFSG.KC.Fam.rowsBasis Vr (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM)
    (CFSG.KC.Ord.validM 5 229957 L H) (CFSG.KC.Ord.validM 5 1729 LV HV) 1729 133 ONE Mir = true := by
  quickRfl

end CFSG.KD.FamHNAlg

end
