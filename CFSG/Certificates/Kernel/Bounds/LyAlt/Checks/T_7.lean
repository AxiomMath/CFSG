module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_7.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_7_J.bin" 199240 15219916382687078781
#kc_repo #kc_items_root CFSG.KD.LyA.T_7.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_7_lo.bin" 94 13216138064445092666
#kc_repo #kc_items_root CFSG.KD.LyA.T_7.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_7_acc.bin" 126 8644941176611778913

namespace CFSG.KD.LyA.T_7

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1 - 182) - lo (i - 182)) (lo (i - 182))) (acc (i - 182)))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1 - 182)) (Nat.succ nT) (Nat.beq i 199))

end CFSG.KD.LyA.T_7

#kc_each_unfold CFSG.KD.LyA.T_7.ok 182 200 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_7.lo CFSG.KD.LyA.T_7.acc

end
