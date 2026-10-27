module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_0_J.bin" 287818 9622132014271056886
#kc_repo #kc_items_root CFSG.KD.LyA.T_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_0_lo.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.LyA.T_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_0_acc.bin" 161 1968168015492393182

namespace CFSG.KD.LyA.T_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.LyA.T_0

#kc_each_unfold CFSG.KD.LyA.T_0.ok 0 26 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_0.lo CFSG.KD.LyA.T_0.acc

end
