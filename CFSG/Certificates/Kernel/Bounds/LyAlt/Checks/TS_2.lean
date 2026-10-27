module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.TS_2.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/TS_2_J.bin" 142619 8771570758689094564
#kc_repo #kc_items_root CFSG.KD.LyA.TS_2.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/TS_2_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.TS_2.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/TS_2_acc.bin" 1155 8909113800003185593

namespace CFSG.KD.LyA.TS_2

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (tS TB) 19 nT
      (seg J (lo (i + 1 - 40) - lo (i - 40)) (lo (i - 40))) (acc (i - 40)))
    (acc (i + 1 - 40))

end CFSG.KD.LyA.TS_2

#kc_each_unfold CFSG.KD.LyA.TS_2.ok 40 60 as CFSG.KD.LyA.ts
  eval CFSG.KD.LyA.TS_2.lo CFSG.KD.LyA.TS_2.acc

end
