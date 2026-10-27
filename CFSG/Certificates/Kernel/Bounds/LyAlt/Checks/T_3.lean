module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_3.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_3_J.bin" 287791 4308607559710846900
#kc_repo #kc_items_root CFSG.KD.LyA.T_3.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_3_lo.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.LyA.T_3.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_3_acc.bin" 189 5112079044747796924

namespace CFSG.KD.LyA.T_3

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1 - 78) - lo (i - 78)) (lo (i - 78))) (acc (i - 78)))
    (acc (i + 1 - 78))

end CFSG.KD.LyA.T_3

#kc_each_unfold CFSG.KD.LyA.T_3.ok 78 104 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_3.lo CFSG.KD.LyA.T_3.acc

end
