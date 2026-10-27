module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.CM12M "keys0.plan.txt" 1970 11942929370219045299
#kc_repo #kc_nat_runs_gz CFSG.KD.CM12M "CFSG/Certificates/Kernel/KDenseP/CM12/Mono0f.items.gz" 1148448 15618860551399106518
  (cn 0 22) (on 0 22) (qn 0 22) (sel 0 22) (xsel 0 22) (wn 0 22) (psw 0 22) (sgX 0 22) (sgW 0 22) (sgA 0 22)

end
