module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M3BM "keys3.plan.txt" 6552 742991419934728420
#kc_repo #kc_nat_runs_gz CFSG.KD.M3BM "CFSG/Certificates/Kernel/KDenseP/MonThreeB/Mono3f.items.gz" 3758826 3232507132173411402
  (cn 216 288) (on 216 288) (qn 216 288) (sel 216 288) (xsel 216 288) (wn 216 288) (psw 216 288) (sgX 216 288) (sgW 216 288) (sgA 216 288)

end
