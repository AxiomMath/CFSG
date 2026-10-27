module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.T_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/T_0_J.bin" 74379 6880440198050252088
#kc_repo #kc_items_root CFSG.KD.HNA.T_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/T_0_lo.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.HNA.T_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/T_0_acc.bin" 41 16121533663930775692

namespace CFSG.KD.HNA.T_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runT TB OB CFSG.KC.HNA.rel LT TL VL NL NR nT I0
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1)) (Nat.succ nT) (Nat.beq i (nat_lit 6)))

end CFSG.KD.HNA.T_0

#kc_each_unfold CFSG.KD.HNA.T_0.ok 0 7 as CFSG.KD.HNA.t
  eval CFSG.KD.HNA.T_0.lo CFSG.KD.HNA.T_0.acc

end
