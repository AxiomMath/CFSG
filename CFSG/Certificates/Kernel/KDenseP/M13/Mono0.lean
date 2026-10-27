module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M13M "keys0.plan.txt" 3410 4126458654388104231
#kc_repo #kc_nat_runs_gz CFSG.KD.M13M "CFSG/Certificates/Kernel/KDenseP/M13/Mono0f.items.gz" 1985032 4724343043247425389
  (cn 0 38) (on 0 38) (qn 0 38) (sel 0 38) (xsel 0 38) (wn 0 38) (psw 0 38) (sgX 0 38) (sgW 0 38) (sgA 0 38)

end
