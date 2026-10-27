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

#kc_repo #kc_items_root CFSG.KD.LyA.ES2_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES2_0_J.bin" 14380 2454947567409230957
#kc_repo #kc_items_root CFSG.KD.LyA.ES2_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES2_0_lo.bin" 19 14667893835390355763
#kc_repo #kc_items_root CFSG.KD.LyA.ES2_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES2_0_acc.bin" 170 3596992034739650101

namespace CFSG.KD.LyA.ES2_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (mat E2) 19 (bits MD 40 20)
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.LyA.ES2_0

#kc_each_unfold CFSG.KD.LyA.ES2_0.ok 0 3 as CFSG.KD.LyA.es2
  eval CFSG.KD.LyA.ES2_0.lo CFSG.KD.LyA.ES2_0.acc

namespace CFSG.KD.LyA

open CFSG.KC.LyA.DceS

theorem es2n : Nat.beq (sortedCount (ES2_0.acc 3)) (bits MD 40 20) = true := by quickRfl

end CFSG.KD.LyA

end
