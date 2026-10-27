module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_1.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_1_J.bin" 359770 15323604053501072783
#kc_repo #kc_items_root CFSG.KD.LyA.W_1.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_1_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.LyA.W_1.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_1_acc.bin" 441 16358722764598535574

namespace CFSG.KD.LyA.W_1

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 48) - lo (i - 48)) (lo (i - 48))) (acc (i - 48)))
    (acc (i + 1 - 48))

end CFSG.KD.LyA.W_1

#kc_each_unfold CFSG.KD.LyA.W_1.ok 48 96 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_1.lo CFSG.KD.LyA.W_1.acc

end
