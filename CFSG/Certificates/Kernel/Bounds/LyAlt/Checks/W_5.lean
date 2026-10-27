module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_5.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_5_J.bin" 348459 10869840342304118470
#kc_repo #kc_items_root CFSG.KD.LyA.W_5.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_5_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.LyA.W_5.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_5_acc.bin" 441 7436452752111782807

namespace CFSG.KD.LyA.W_5

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 240) - lo (i - 240)) (lo (i - 240))) (acc (i - 240)))
    (acc (i + 1 - 240))

end CFSG.KD.LyA.W_5

#kc_each_unfold CFSG.KD.LyA.W_5.ok 240 288 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_5.lo CFSG.KD.LyA.W_5.acc

end
