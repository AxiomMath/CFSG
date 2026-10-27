module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys7.plan.txt" 17112 16399776480135160610
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono7f.items.gz" 9709323 16477954864759656638
  (cn 1302 1488) (on 1302 1488) (qn 1302 1488) (sel 1302 1488) (xsel 1302 1488) (wn 1302 1488) (psw 1302 1488) (sgX 1302 1488) (sgW 1302 1488) (sgA 1302 1488)

end
