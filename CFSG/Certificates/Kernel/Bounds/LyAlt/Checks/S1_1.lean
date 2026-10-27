module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.S1_1.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_1_J.bin" 180118 13371770713477258455
#kc_repo #kc_items_root CFSG.KD.LyA.S1_1.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_1_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.S1_1.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_1_acc.bin" 145 15891784197487722657

namespace CFSG.KD.LyA.S1_1

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runStab FB E1 5 816 NF 1 SG1
      (seg J (lo (i + 1 - 20) - lo (i - 20)) (lo (i - 20))) (acc (i - 20)))
    (acc (i + 1 - 20))

end CFSG.KD.LyA.S1_1

#kc_each_unfold CFSG.KD.LyA.S1_1.ok 20 40 as CFSG.KD.LyA.s1
  eval CFSG.KD.LyA.S1_1.lo CFSG.KD.LyA.S1_1.acc

end
