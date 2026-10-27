module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys4.plan.txt" 16926 5577060354514385205
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono4f.items.gz" 9711525 1676333141862292508
  (cn 744 930) (on 744 930) (qn 744 930) (sel 744 930) (xsel 744 930) (wn 744 930) (psw 744 930) (sgX 744 930) (sgW 744 930) (sgA 744 930)

end
