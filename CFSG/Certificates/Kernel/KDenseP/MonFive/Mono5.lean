module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys5.plan.txt" 17042 3312033727130386956
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono5f.items.gz" 9702430 5661813566240544809
  (cn 930 1116) (on 930 1116) (qn 930 1116) (sel 930 1116) (xsel 930 1116) (wn 930 1116) (psw 930 1116) (sgX 930 1116) (sgW 930 1116) (sgA 930 1116)

end
