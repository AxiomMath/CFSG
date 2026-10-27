module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.MWM "keys0.plan.txt" 2150 43407269793987262
#kc_repo #kc_nat_runs_gz CFSG.KD.MWM "CFSG/Certificates/Kernel/KDenseP/MW/Mono0f.items.gz" 1253884 15869477170811263273
  (cn 0 24) (on 0 24) (qn 0 24) (sel 0 24) (xsel 0 24) (wn 0 24) (psw 0 24) (sgX 0 24) (sgW 0 24) (sgA 0 24)

end
