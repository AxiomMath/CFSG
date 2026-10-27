module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys0.plan.txt" 8990 1531337004467520694
#kc_repo #kc_nat_runs_gz CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono0f.items.gz" 5219266 9037019824831685772
  (cn 0 100) (on 0 100) (qn 0 100) (sel 0 100) (xsel 0 100) (wn 0 100) (psw 0 100) (sgX 0 100) (sgW 0 100) (sgA 0 100)

end
