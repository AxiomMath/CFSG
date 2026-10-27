module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_4.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_4_J.bin" 287791 98921851085791026
#kc_repo #kc_items_root CFSG.KD.LyA.T_4.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_4_lo.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.LyA.T_4.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_4_acc.bin" 189 5355394491942843591

namespace CFSG.KD.LyA.T_4

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1 - 104) - lo (i - 104)) (lo (i - 104))) (acc (i - 104)))
    (acc (i + 1 - 104))

end CFSG.KD.LyA.T_4

#kc_each_unfold CFSG.KD.LyA.T_4.ok 104 130 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_4.lo CFSG.KD.LyA.T_4.acc

end
