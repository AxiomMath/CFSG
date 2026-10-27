module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.W_9.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_9_J.bin" 65761 5085413864463291616
#kc_repo #kc_items_root CFSG.KD.LyA.W_9.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_9_lo.bin" 44 14070430467677855285
#kc_repo #kc_items_root CFSG.KD.LyA.W_9.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/W_9_acc.bin" 72 18271181271672480231

namespace CFSG.KD.LyA.W_9

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD 5 816 LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1 - 432) - lo (i - 432)) (lo (i - 432))) (acc (i - 432)))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1 - 432)) (mkS NF ND) (Nat.beq i 439))

end CFSG.KD.LyA.W_9

#kc_each_unfold CFSG.KD.LyA.W_9.ok 432 440 as CFSG.KD.LyA.w
  eval CFSG.KD.LyA.W_9.lo CFSG.KD.LyA.W_9.acc

end
