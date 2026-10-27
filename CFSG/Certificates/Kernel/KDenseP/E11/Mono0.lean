module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.E11M "keys0.plan.txt" 2870 17846987567114167978
#kc_repo #kc_nat_runs_gz CFSG.KD.E11M "CFSG/Certificates/Kernel/KDenseP/E11/Mono0f.items.gz" 1669084 651759253564814471
  (cn 0 32) (on 0 32) (qn 0 32) (sel 0 32) (xsel 0 32) (wn 0 32) (psw 0 32) (sgX 0 32) (sgW 0 32) (sgA 0 32)

end
