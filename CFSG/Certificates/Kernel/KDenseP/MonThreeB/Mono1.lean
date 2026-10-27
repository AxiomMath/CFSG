module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M3BM "keys1.plan.txt" 6524 6038910988115641715
#kc_repo #kc_nat_runs_gz CFSG.KD.M3BM "CFSG/Certificates/Kernel/KDenseP/MonThreeB/Mono1f.items.gz" 3755226 5615306785879712392
  (cn 72 144) (on 72 144) (qn 72 144) (sel 72 144) (xsel 72 144) (wn 72 144) (psw 72 144) (sgX 72 144) (sgW 72 144) (sgA 72 144)

end
