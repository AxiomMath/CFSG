module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.C_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/C_0_J.bin" 52627 2499264754135554967
#kc_repo #kc_items_root CFSG.KD.LyA.C_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/C_0_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.LyA.C_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/C_0_acc.bin" 126 15201491510912755543

namespace CFSG.KD.LyA.C_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runCover FB OB 5 816 NF NO AL
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.LyA.C_0

#kc_each_unfold CFSG.KD.LyA.C_0.ok 0 20 as CFSG.KD.LyA.c
  eval CFSG.KD.LyA.C_0.lo CFSG.KD.LyA.C_0.acc

end
