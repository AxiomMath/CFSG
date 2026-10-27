module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_7.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_7_J.bin" 359306 11334283581179564198
#kc_repo #kc_items_root CFSG.KD.LyA.W_7.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_7_lo.bin" 273 1490644700736047833
#kc_repo #kc_items_root CFSG.KD.LyA.W_7.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_7_acc.bin" 441 1636516608017206753

namespace CFSG.KD.LyA.W_7

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 336) - lo (i - 336)) (lo (i - 336))) (acc (i - 336)))
    (acc (i + 1 - 336))

end CFSG.KD.LyA.W_7

#kc_each_unfold CFSG.KD.LyA.W_7.ok 336 384 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_7.lo CFSG.KD.LyA.W_7.acc

end
