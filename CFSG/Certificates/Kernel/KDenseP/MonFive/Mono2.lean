module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys2.plan.txt" 16926 11078852610325545960
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono2f.items.gz" 9716601 1897242201227665228
  (cn 372 558) (on 372 558) (qn 372 558) (sel 372 558) (xsel 372 558) (wn 372 558) (psw 372 558) (sgX 372 558) (sgW 372 558) (sgA 372 558)

end
