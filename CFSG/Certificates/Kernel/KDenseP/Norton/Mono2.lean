module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.NRTM "keys2.plan.txt" 6552 7427825520139894559
#kc_repo #kc_nat_runs_gz CFSG.KD.NRTM "CFSG/Certificates/Kernel/KDenseP/Norton/Mono2f.items.gz" 3756628 13606795368296923232
  (cn 144 216) (on 144 216) (qn 144 216) (sel 144 216) (xsel 144 216) (wn 144 216) (psw 144 216) (sgX 144 216) (sgW 144 216) (sgA 144 216)

end
