module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5BM "keys0.plan.txt" 6470 13156237565717793169
#kc_repo #kc_nat_runs_gz CFSG.KD.M5BM "CFSG/Certificates/Kernel/KDenseP/MonFiveB/Mono0f.items.gz" 3756152 4137415148282138790
  (cn 0 72) (on 0 72) (qn 0 72) (sel 0 72) (xsel 0 72) (wn 0 72) (psw 0 72) (sgX 0 72) (sgW 0 72) (sgA 0 72)

end
