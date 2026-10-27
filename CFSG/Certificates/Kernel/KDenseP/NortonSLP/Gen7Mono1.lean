module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen7M "Gen7keys1.plan.txt" 23296 3770252707836565234
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.Gen7M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/Gen7Mono1f.items.gz" 13363252 1438286931544922607
  (cn 256 512) (on 256 512) (qn 256 512) (sel 256 512) (xsel 256 512) (wn 256 512) (psw 256 512) (sgX 256 512) (sgW 256 512) (sgA 256 512)

end
