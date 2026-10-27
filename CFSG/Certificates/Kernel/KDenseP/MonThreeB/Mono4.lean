module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M3BM "keys4.plan.txt" 6552 11984037073067461371
#kc_repo #kc_nat_runs_gz CFSG.KD.M3BM "CFSG/Certificates/Kernel/KDenseP/MonThreeB/Mono4f.items.gz" 3759260 16583150862825935547
  (cn 288 360) (on 288 360) (qn 288 360) (sel 288 360) (xsel 288 360) (wn 288 360) (psw 288 360) (sgX 288 360) (sgW 288 360) (sgA 288 360)

end
