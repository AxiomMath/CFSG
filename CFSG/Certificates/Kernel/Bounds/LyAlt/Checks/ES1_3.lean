module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.ES1_3.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES1_3_J.bin" 142620 4790580791751418514
#kc_repo #kc_items_root CFSG.KD.LyA.ES1_3.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES1_3_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.ES1_3.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/ES1_3_acc.bin" 1155 9938640099742301639

namespace CFSG.KD.LyA.ES1_3

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (mat E1) 19 (bits MD 20 20)
      (seg J (lo (i + 1 - 60) - lo (i - 60)) (lo (i - 60))) (acc (i - 60)))
    (acc (i + 1 - 60))

end CFSG.KD.LyA.ES1_3

#kc_each_unfold CFSG.KD.LyA.ES1_3.ok 60 80 as CFSG.KD.LyA.es1
  eval CFSG.KD.LyA.ES1_3.lo CFSG.KD.LyA.ES1_3.acc

end
