module

public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.Kernel.Fam.LySeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.FamLySeed "CFSG/Certificates/Kernel/Fam/LySeed/Data/slp.json.gz" 244
  16791847667101360446 (SW : List Nat)

public noncomputable section

namespace CFSG.KD.FamLySeed

theorem ws : Nat.beq (CFSG.KC.Ord.runSlp RW (CFSG.KC.Ord.mulR 5 12 1332 111 8 L H CM RM)
    (CFSG.KC.Ord.validM 5 147852 L H) ONE SW 3) 19 = true := by
  quickRfl

end CFSG.KD.FamLySeed

end
