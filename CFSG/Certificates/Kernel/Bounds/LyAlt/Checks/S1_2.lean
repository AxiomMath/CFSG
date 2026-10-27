module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.S1_2.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_2_J.bin" 180120 6912236628782067120
#kc_repo #kc_items_root CFSG.KD.LyA.S1_2.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_2_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.S1_2.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S1_2_acc.bin" 147 12634910017485197945

namespace CFSG.KD.LyA.S1_2

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runStab FB E1 5 816 NF 1 SG1
      (seg J (lo (i + 1 - 40) - lo (i - 40)) (lo (i - 40))) (acc (i - 40)))
    (acc (i + 1 - 40))

end CFSG.KD.LyA.S1_2

#kc_each_unfold CFSG.KD.LyA.S1_2.ok 40 60 as CFSG.KD.LyA.s1
  eval CFSG.KD.LyA.S1_2.lo CFSG.KD.LyA.S1_2.acc

end
