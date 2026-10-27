module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.J4.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.FamJ4 "CFSG/Certificates/Kernel/Fam/J4/Data/slp.json.gz" 3490
  4069663066309220340 (S0 : List Nat)

public noncomputable section

namespace CFSG.KD.FamJ4

theorem ws0 : Nat.beq (CFSG.KC.Ord.runSlp RW (CFSG.KC.Ord.mulR 2 8 896 112 5 L H CM RM)
    (CFSG.KC.Ord.validM 2 100352 L H) ONE S0 3) 99 = true := by
  quickRfl

end CFSG.KD.FamJ4

end
