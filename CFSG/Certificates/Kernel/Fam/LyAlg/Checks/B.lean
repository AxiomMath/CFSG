module

public import CFSG.Certificates.Kernel.Fam.Cent
public import CFSG.Certificates.Kernel.Fam.LyAlg.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fam.Act

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.FamLyAlg

theorem treec : CFSG.KC.Fam.treeVecOK Vc (CFSG.KC.Ord.vecR 5 12 1332 111 8 LV HV RM) (RW 3) (RW 4)
    vrow PTc 111 = true := by
  quickRfl

theorem basisc : CFSG.KC.Fam.rowsBasis Vc (CFSG.KC.Ord.mulR 5 12 1332 111 8 L H CM RM)
    (CFSG.KC.Ord.validM 5 147852 L H) (CFSG.KC.Ord.validM 5 1332 LV HV) 1332 111 ONE Mic = true := by
  quickRfl

end CFSG.KD.FamLyAlg

end
