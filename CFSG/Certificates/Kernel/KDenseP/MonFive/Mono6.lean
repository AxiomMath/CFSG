module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys6.plan.txt" 17112 3918822784330907165
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono6f.items.gz" 9714694 5545386149574113269
  (cn 1116 1302) (on 1116 1302) (qn 1116 1302) (sel 1116 1302) (xsel 1116 1302) (wn 1116 1302) (psw 1116 1302) (sgX 1116 1302) (sgW 1116 1302) (sgA 1116 1302)

end
