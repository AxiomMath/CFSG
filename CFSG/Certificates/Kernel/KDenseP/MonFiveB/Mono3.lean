module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5BM "keys3.plan.txt" 6552 14621434312724596002
#kc_repo #kc_nat_runs_gz CFSG.KD.M5BM "CFSG/Certificates/Kernel/KDenseP/MonFiveB/Mono3f.items.gz" 3753348 5256585111278557573
  (cn 216 288) (on 216 288) (qn 216 288) (sel 216 288) (xsel 216 288) (wn 216 288) (psw 216 288) (sgX 216 288) (sgW 216 288) (sgA 216 288)

end
