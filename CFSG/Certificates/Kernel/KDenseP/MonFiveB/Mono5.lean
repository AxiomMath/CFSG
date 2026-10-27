module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5BM "keys5.plan.txt" 6552 12360870672659071673
#kc_repo #kc_nat_runs_gz CFSG.KD.M5BM "CFSG/Certificates/Kernel/KDenseP/MonFiveB/Mono5f.items.gz" 3758039 17942419376497035240
  (cn 360 432) (on 360 432) (qn 360 432) (sel 360 432) (xsel 360 432) (wn 360 432) (psw 360 432) (sgX 360 432) (sgW 360 432) (sgA 360 432)

end
