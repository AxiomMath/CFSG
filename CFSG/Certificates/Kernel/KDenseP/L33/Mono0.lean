module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.L33M "keys0.plan.txt" 1700 1726605422519983220
#kc_repo #kc_nat_runs_gz CFSG.KD.L33M "CFSG/Certificates/Kernel/KDenseP/L33/Mono0f.items.gz" 976195 3374761745245743046
  (cn 0 19) (on 0 19) (qn 0 19) (sel 0 19) (xsel 0 19) (wn 0 19) (psw 0 19) (sgX 0 19) (sgW 0 19) (sgA 0 19)

end
