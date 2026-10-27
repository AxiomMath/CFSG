module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen7M "Gen7keys0.plan.txt" 23186 11946989523047348690
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.Gen7M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/Gen7Mono0f.items.gz" 13340313 5499422079071706150
  (cn 0 256) (on 0 256) (qn 0 256) (sel 0 256) (xsel 0 256) (wn 0 256) (psw 0 256) (sgX 0 256) (sgW 0 256) (sgA 0 256)

end
