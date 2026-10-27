module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys1.plan.txt" 16926 1605507238327042438
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono1f.items.gz" 9710643 6937418743019777554
  (cn 186 372) (on 186 372) (qn 186 372) (sel 186 372) (xsel 186 372) (wn 186 372) (psw 186 372) (sgX 186 372) (sgW 186 372) (sgA 186 372)

end
