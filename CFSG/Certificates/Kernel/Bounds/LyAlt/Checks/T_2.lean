module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_2.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_2_J.bin" 287791 11508285811630817016
#kc_repo #kc_items_root CFSG.KD.LyA.T_2.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_2_lo.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.LyA.T_2.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_2_acc.bin" 189 12123824722888303853

namespace CFSG.KD.LyA.T_2

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1 - 52) - lo (i - 52)) (lo (i - 52))) (acc (i - 52)))
    (acc (i + 1 - 52))

end CFSG.KD.LyA.T_2

#kc_each_unfold CFSG.KD.LyA.T_2.ok 52 78 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_2.lo CFSG.KD.LyA.T_2.acc

end
