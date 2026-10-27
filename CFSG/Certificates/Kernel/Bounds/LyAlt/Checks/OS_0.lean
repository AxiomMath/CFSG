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

#kc_repo #kc_items_root CFSG.KD.LyA.OS_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/OS_0_J.bin" 36661 14136378107138069748
#kc_repo #kc_items_root CFSG.KD.LyA.OS_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/OS_0_lo.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.LyA.OS_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/OS_0_acc.bin" 341 10558177168126112020

namespace CFSG.KD.LyA.OS_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (pt OB) 15 NO
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.LyA.OS_0

#kc_each_unfold CFSG.KD.LyA.OS_0.ok 0 7 as CFSG.KD.LyA.os
  eval CFSG.KD.LyA.OS_0.lo CFSG.KD.LyA.OS_0.acc

namespace CFSG.KD.LyA

open CFSG.KC.LyA.DceS

theorem osn : Nat.beq (sortedCount (OS_0.acc 7)) NO = true := by quickRfl

end CFSG.KD.LyA

end
