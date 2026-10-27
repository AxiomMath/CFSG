module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M3BM "keys5.plan.txt" 5005 9634280595638617281
#kc_repo #kc_nat_runs_gz CFSG.KD.M3BM "CFSG/Certificates/Kernel/KDenseP/MonThreeB/Mono5f.items.gz" 2875011 7988311107456881247
  (cn 360 415) (on 360 415) (qn 360 415) (sel 360 415) (xsel 360 415) (wn 360 415) (psw 360 415) (sgX 360 415) (sgW 360 415) (sgA 360 415)

end
