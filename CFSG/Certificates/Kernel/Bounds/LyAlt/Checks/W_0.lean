module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_0_J.bin" 417779 11466299059748710177
#kc_repo #kc_items_root CFSG.KD.LyA.W_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_0_lo.bin" 286 10217295813799494767
#kc_repo #kc_items_root CFSG.KD.LyA.W_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_0_acc.bin" 441 6432002831872252638

namespace CFSG.KD.LyA.W_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.LyA.W_0

#kc_each_unfold CFSG.KD.LyA.W_0.ok 0 48 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_0.lo CFSG.KD.LyA.W_0.acc

end
