module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.G_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/G_0_J.bin" 5 393272179552599003
#kc_repo #kc_items_root CFSG.KD.HNA.G_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/G_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.HNA.G_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/G_0_acc.bin" 5 16058875513670357405

namespace CFSG.KD.HNA.G_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runGom HB GB OB I0 nH
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Nat.succ NO)

end CFSG.KD.HNA.G_0

#kc_each_unfold CFSG.KD.HNA.G_0.ok 0 1 as CFSG.KD.HNA.g
  eval CFSG.KD.HNA.G_0.lo CFSG.KD.HNA.G_0.acc

end
