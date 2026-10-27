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

#kc_repo #kc_items_root CFSG.KD.LyA.ES4_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES4_0_J.bin" 6845 17616679891514065522
#kc_repo #kc_items_root CFSG.KD.LyA.ES4_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES4_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.LyA.ES4_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES4_0_acc.bin" 60 863147875050289925

namespace CFSG.KD.LyA.ES4_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (mat E4) 19 (bits MD 80 20)
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.LyA.ES4_0

#kc_each_unfold CFSG.KD.LyA.ES4_0.ok 0 1 as CFSG.KD.LyA.es4
  eval CFSG.KD.LyA.ES4_0.lo CFSG.KD.LyA.ES4_0.acc

namespace CFSG.KD.LyA

open CFSG.KC.LyA.DceS

theorem es4n : Nat.beq (sortedCount (ES4_0.acc 1)) (bits MD 80 20) = true := by quickRfl

end CFSG.KD.LyA

end
