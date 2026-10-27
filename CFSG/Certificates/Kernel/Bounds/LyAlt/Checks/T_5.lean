module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_5.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_5_J.bin" 287793 7751153640672699309
#kc_repo #kc_items_root CFSG.KD.LyA.T_5.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_5_lo.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.LyA.T_5.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_5_acc.bin" 189 10306642983001317610

namespace CFSG.KD.LyA.T_5

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1 - 130) - lo (i - 130)) (lo (i - 130))) (acc (i - 130)))
    (acc (i + 1 - 130))

end CFSG.KD.LyA.T_5

#kc_each_unfold CFSG.KD.LyA.T_5.ok 130 156 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_5.lo CFSG.KD.LyA.T_5.acc

end
