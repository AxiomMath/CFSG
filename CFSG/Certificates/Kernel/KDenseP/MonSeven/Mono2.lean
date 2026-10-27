module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys2.plan.txt" 9100 2431961349709132194
#kc_repo #kc_nat_runs_gz CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono2f.items.gz" 5220666 18322488737568805219
  (cn 200 300) (on 200 300) (qn 200 300) (sel 200 300) (xsel 200 300) (wn 200 300) (psw 200 300) (sgX 200 300) (sgW 200 300) (sgA 200 300)

end
