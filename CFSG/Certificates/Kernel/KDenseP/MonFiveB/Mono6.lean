module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5BM "keys6.plan.txt" 6552 9065311973466377486
#kc_repo #kc_nat_runs_gz CFSG.KD.M5BM "CFSG/Certificates/Kernel/KDenseP/MonFiveB/Mono6f.items.gz" 3755415 6436432078255939655
  (cn 432 504) (on 432 504) (qn 432 504) (sel 432 504) (xsel 432 504) (wn 432 504) (psw 432 504) (sgX 432 504) (sgW 432 504) (sgA 432 504)

end
