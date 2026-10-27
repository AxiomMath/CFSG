module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.DA7M "keys0.plan.txt" 3500 15720277780657385760
#kc_repo #kc_nat_runs_gz CFSG.KD.DA7M "CFSG/Certificates/Kernel/KDenseP/DenseAlign/Mono0f.items.gz" 2034165 14844490227946456978
  (cn 0 39) (on 0 39) (qn 0 39) (sel 0 39) (xsel 0 39) (wn 0 39) (psw 0 39) (sgX 0 39) (sgW 0 39) (sgA 0 39)

end
