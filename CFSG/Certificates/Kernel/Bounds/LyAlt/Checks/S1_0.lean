module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.S1_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_0_J.bin" 180118 8854156153046146974
#kc_repo #kc_items_root CFSG.KD.LyA.S1_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_0_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.S1_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_0_acc.bin" 125 6687453186404925289

namespace CFSG.KD.LyA.S1_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runStab FB E1 5 816 NF 1 SG1
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.LyA.S1_0

#kc_each_unfold CFSG.KD.LyA.S1_0.ok 0 20 as CFSG.KD.LyA.s1
  eval CFSG.KD.LyA.S1_0.lo CFSG.KD.LyA.S1_0.acc

end
