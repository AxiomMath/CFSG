module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_3.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_3_J.bin" 383993 17604599080743667478
#kc_repo #kc_items_root CFSG.KD.LyA.W_3.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_3_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.LyA.W_3.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_3_acc.bin" 441 4935426622473462757

namespace CFSG.KD.LyA.W_3

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 144) - lo (i - 144)) (lo (i - 144))) (acc (i - 144)))
    (acc (i + 1 - 144))

end CFSG.KD.LyA.W_3

#kc_each_unfold CFSG.KD.LyA.W_3.ok 144 192 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_3.lo CFSG.KD.LyA.W_3.acc

end
