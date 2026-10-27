module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys0.plan.txt" 16816 5158974118556123209
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono0f.items.gz" 9709323 5650193862345332608
  (cn 0 186) (on 0 186) (qn 0 186) (sel 0 186) (xsel 0 186) (wn 0 186) (psw 0 186) (sgX 0 186) (sgW 0 186) (sgA 0 186)

end
