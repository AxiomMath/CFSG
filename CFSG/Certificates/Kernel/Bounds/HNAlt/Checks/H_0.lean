module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.H_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/H_0_J.bin" 111342 1489816958634135044
#kc_repo #kc_items_root CFSG.KD.HNA.H_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/H_0_lo.bin" 59 17425217917344080136
#kc_repo #kc_items_root CFSG.KD.HNA.H_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/H_0_acc.bin" 65 4707322839498762975

namespace CFSG.KD.HNA.H_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runHdr HB LT TL VL NL
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1)) (Nat.succ nH) (Nat.beq i (nat_lit 10)))

end CFSG.KD.HNA.H_0

#kc_each_unfold CFSG.KD.HNA.H_0.ok 0 11 as CFSG.KD.HNA.h
  eval CFSG.KD.HNA.H_0.lo CFSG.KD.HNA.H_0.acc

end
