module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_6.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_6_J.bin" 287794 1025789921782808459
#kc_repo #kc_items_root CFSG.KD.LyA.T_6.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_6_lo.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.LyA.T_6.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_6_acc.bin" 189 4767998384471872054

namespace CFSG.KD.LyA.T_6

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1 - 156) - lo (i - 156)) (lo (i - 156))) (acc (i - 156)))
    (acc (i + 1 - 156))

end CFSG.KD.LyA.T_6

#kc_each_unfold CFSG.KD.LyA.T_6.ok 156 182 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_6.lo CFSG.KD.LyA.T_6.acc

end
