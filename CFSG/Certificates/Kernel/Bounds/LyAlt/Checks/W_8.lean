module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_8.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_8_J.bin" 408137 8775937980769524627
#kc_repo #kc_items_root CFSG.KD.LyA.W_8.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_8_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.LyA.W_8.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_8_acc.bin" 441 9743159734747167302

namespace CFSG.KD.LyA.W_8

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 384) - lo (i - 384)) (lo (i - 384))) (acc (i - 384)))
    (acc (i + 1 - 384))

end CFSG.KD.LyA.W_8

#kc_each_unfold CFSG.KD.LyA.W_8.ok 384 432 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_8.lo CFSG.KD.LyA.W_8.acc

end
