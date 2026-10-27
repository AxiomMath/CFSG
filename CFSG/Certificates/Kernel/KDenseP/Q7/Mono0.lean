module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.Q7M "keys0.plan.txt" 712 9533251633672138895
#kc_repo #kc_nat_runs_gz CFSG.KD.Q7M "CFSG/Certificates/Kernel/KDenseP/Q7/Mono0f.items.gz" 417286 18365201422265280215
  (cn 0 8) (on 0 8) (qn 0 8) (sel 0 8) (xsel 0 8) (wn 0 8) (psw 0 8) (sgX 0 8) (sgW 0 8) (sgA 0 8)

end
