module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.S1_4.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_4_J.bin" 180117 9394788800249296997
#kc_repo #kc_items_root CFSG.KD.LyA.S1_4.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_4_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.S1_4.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_4_acc.bin" 140 10208827641791217052

namespace CFSG.KD.LyA.S1_4

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runStab FB E1 5 816 NF 1 SG1
      (seg J (lo (i + 1 - 80) - lo (i - 80)) (lo (i - 80))) (acc (i - 80)))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1 - 80)) (Nat.succ (bits MD 20 20))
      (Nat.beq i 99))

end CFSG.KD.LyA.S1_4

#kc_each_unfold CFSG.KD.LyA.S1_4.ok 80 100 as CFSG.KD.LyA.s1
  eval CFSG.KD.LyA.S1_4.lo CFSG.KD.LyA.S1_4.acc

end
