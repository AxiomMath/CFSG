module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.T_1.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_1_J.bin" 287791 18290960746215099138
#kc_repo #kc_items_root CFSG.KD.LyA.T_1.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_1_lo.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.LyA.T_1.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/T_1_acc.bin" 171 7042757183935942762

namespace CFSG.KD.LyA.T_1

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.LyA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1 - 26) - lo (i - 26)) (lo (i - 26))) (acc (i - 26)))
    (acc (i + 1 - 26))

end CFSG.KD.LyA.T_1

#kc_each_unfold CFSG.KD.LyA.T_1.ok 26 52 as CFSG.KD.LyA.t
  eval CFSG.KD.LyA.T_1.lo CFSG.KD.LyA.T_1.acc

end
