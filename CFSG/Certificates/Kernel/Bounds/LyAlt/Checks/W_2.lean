module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_2.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_2_J.bin" 345903 2728643729415904162
#kc_repo #kc_items_root CFSG.KD.LyA.W_2.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_2_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.LyA.W_2.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_2_acc.bin" 441 12321361684036395037

namespace CFSG.KD.LyA.W_2

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 96) - lo (i - 96)) (lo (i - 96))) (acc (i - 96)))
    (acc (i + 1 - 96))

end CFSG.KD.LyA.W_2

#kc_each_unfold CFSG.KD.LyA.W_2.ok 96 144 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_2.lo CFSG.KD.LyA.W_2.acc

end
