module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys5.plan.txt" 9100 16579714636393677535
#kc_repo #kc_nat_runs_gz CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono5f.items.gz" 5219457 12582623657962671940
  (cn 500 600) (on 500 600) (qn 500 600) (sel 500 600) (xsel 500 600) (wn 500 600) (psw 500 600) (sgX 500 600) (sgW 500 600) (sgA 500 600)

end
