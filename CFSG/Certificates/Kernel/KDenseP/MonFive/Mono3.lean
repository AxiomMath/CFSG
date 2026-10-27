module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M5RM "keys3.plan.txt" 16926 3730434995105742294
#kc_repo #kc_nat_runs_gz CFSG.KD.M5RM "CFSG/Certificates/Kernel/KDenseP/MonFive/Mono3f.items.gz" 9708592 12716838426690003667
  (cn 558 744) (on 558 744) (qn 558 744) (sel 558 744) (xsel 558 744) (wn 558 744) (psw 558 744) (sgX 558 744) (sgW 558 744) (sgA 558 744)

end
