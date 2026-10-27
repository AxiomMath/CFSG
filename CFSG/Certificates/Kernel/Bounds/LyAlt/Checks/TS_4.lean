module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KD.LyA.TS_4.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/TS_4_J.bin" 142620 6300236612077018478
#kc_repo #kc_items_root CFSG.KD.LyA.TS_4.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/TS_4_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.TS_4.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/TS_4_acc.bin" 1155 3816931797298930574

namespace CFSG.KD.LyA.TS_4

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (tS TB) 19 nT
      (seg J (lo (i + 1 - 80) - lo (i - 80)) (lo (i - 80))) (acc (i - 80)))
    (acc (i + 1 - 80))

end CFSG.KD.LyA.TS_4

#kc_each_unfold CFSG.KD.LyA.TS_4.ok 80 100 as CFSG.KD.LyA.ts
  eval CFSG.KD.LyA.TS_4.lo CFSG.KD.LyA.TS_4.acc

namespace CFSG.KD.LyA

open CFSG.KC.LyA.DceS

theorem tsn : Nat.beq (sortedCount (TS_4.acc 20)) nT = true := by quickRfl

end CFSG.KD.LyA

end
