module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys4.plan.txt" 9100 5259241818668884276
#kc_repo #kc_nat_runs_gz CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono4f.items.gz" 5219582 16680265564865430827
  (cn 400 500) (on 400 500) (qn 400 500) (sel 400 500) (xsel 400 500) (wn 400 500) (psw 400 500) (sgX 400 500) (sgW 400 500) (sgA 400 500)

end
