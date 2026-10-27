module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys3.plan.txt" 9100 13864850316296224685
#kc_repo #kc_nat_runs_gz CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono3f.items.gz" 5218388 15696302698154907950
  (cn 300 400) (on 300 400) (qn 300 400) (sel 300 400) (xsel 300 400) (wn 300 400) (psw 300 400) (sgX 300 400) (sgW 300 400) (sgA 300 400)

end
