module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5BM "keys2.plan.txt" 6552 3294310979545278089
#kc_repo #kc_nat_runs_gz CFSG.KD.M5BM "CFSG/Certificates/Kernel/KDenseP/MonFiveB/Mono2f.items.gz" 3755898 6660345088234691676
  (cn 144 216) (on 144 216) (qn 144 216) (sel 144 216) (xsel 144 216) (wn 144 216) (psw 144 216) (sgX 144 216) (sgW 144 216) (sgA 144 216)

end
