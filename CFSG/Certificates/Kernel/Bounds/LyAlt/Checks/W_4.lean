module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_4.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_4_J.bin" 408459 17771022183964396995
#kc_repo #kc_items_root CFSG.KD.LyA.W_4.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_4_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.LyA.W_4.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_4_acc.bin" 441 1199599561301114441

namespace CFSG.KD.LyA.W_4

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 192) - lo (i - 192)) (lo (i - 192))) (acc (i - 192)))
    (acc (i + 1 - 192))

end CFSG.KD.LyA.W_4

#kc_each_unfold CFSG.KD.LyA.W_4.ok 192 240 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_4.lo CFSG.KD.LyA.W_4.acc

end
