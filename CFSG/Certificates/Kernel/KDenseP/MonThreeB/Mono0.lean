module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M3BM "keys0.plan.txt" 6470 5126623176726629347
#kc_repo #kc_nat_runs_gz CFSG.KD.M3BM "CFSG/Certificates/Kernel/KDenseP/MonThreeB/Mono0f.items.gz" 3759567 1415771574750694283
  (cn 0 72) (on 0 72) (qn 0 72) (sel 0 72) (xsel 0 72) (wn 0 72) (psw 0 72) (sgX 0 72) (sgW 0 72) (sgA 0 72)

end
