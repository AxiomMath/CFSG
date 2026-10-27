module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen7M "Gen7keys2.plan.txt" 10374 10713470612232169857
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.Gen7M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/Gen7Mono2f.items.gz" 5950490 1029473867530117852
  (cn 512 626) (on 512 626) (qn 512 626) (sel 512 626) (xsel 512 626) (wn 512 626) (psw 512 626) (sgX 512 626) (sgW 512 626) (sgA 512 626)

end
