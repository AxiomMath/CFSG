module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.FamHNSeed "CFSG/Certificates/Kernel/Fam/HNSeed/Data/slp.json.gz" 269
  11810038031400409094 (SW : List Nat)

public noncomputable section

namespace CFSG.KD.FamHNSeed

theorem ws : Nat.beq (CFSG.KC.Ord.runSlp RW (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM)
    (CFSG.KC.Ord.validM 5 229957 L H) ONE SW 3) 21 = true := by
  quickRfl

end CFSG.KD.FamHNSeed

end
