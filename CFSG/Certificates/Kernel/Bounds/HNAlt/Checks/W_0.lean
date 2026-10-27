module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.W_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/W_0_J.bin" 419463 408722286654652499
#kc_repo #kc_items_root CFSG.KD.HNA.W_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/W_0_lo.bin" 267 6797771413572291884
#kc_repo #kc_items_root CFSG.KD.HNA.W_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/W_0_acc.bin" 432 16230677779938825626

namespace CFSG.KD.HNA.W_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD (nat_lit 5) (nat_lit 708) LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.HNA.W_0

#kc_each_unfold CFSG.KD.HNA.W_0.ok 0 47 as CFSG.KD.HNA.w
  eval CFSG.KD.HNA.W_0.lo CFSG.KD.HNA.W_0.acc

end
