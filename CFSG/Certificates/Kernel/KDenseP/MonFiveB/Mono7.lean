module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5BM "keys7.plan.txt" 5187 7344399378361214449
#kc_repo #kc_nat_runs_gz CFSG.KD.M5BM "CFSG/Certificates/Kernel/KDenseP/MonFiveB/Mono7f.items.gz" 2976952 11227963862753620421
  (cn 504 561) (on 504 561) (qn 504 561) (sel 504 561) (xsel 504 561) (wn 504 561) (psw 504 561) (sgX 504 561) (sgW 504 561) (sgA 504 561)

end
