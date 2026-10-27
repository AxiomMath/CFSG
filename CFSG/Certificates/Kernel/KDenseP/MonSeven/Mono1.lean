module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys1.plan.txt" 9100 8865044650377930323
#kc_repo #kc_nat_runs_gz CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono1f.items.gz" 5215014 9265401862638856862
  (cn 100 200) (on 100 200) (qn 100 200) (sel 100 200) (xsel 100 200) (wn 100 200) (psw 100 200) (sgX 100 200) (sgW 100 200) (sgA 100 200)

end
