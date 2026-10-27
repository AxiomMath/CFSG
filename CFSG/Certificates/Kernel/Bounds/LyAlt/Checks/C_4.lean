module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.C_4.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/C_4_J.bin" 46455 10106250551763101721
#kc_repo #kc_items_root CFSG.KD.LyA.C_4.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/C_4_lo.bin" 94 13216138064445092666
#kc_repo #kc_items_root CFSG.KD.LyA.C_4.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/C_4_acc.bin" 126 17067239515851465208

namespace CFSG.KD.LyA.C_4

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runCover FB OB 5 816 NF NO AL
      (seg J (lo (i + 1 - 80) - lo (i - 80)) (lo (i - 80))) (acc (i - 80)))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1 - 80)) (Nat.add 1 (Nat.shiftLeft ND 20))
      (Nat.beq i 97))

end CFSG.KD.LyA.C_4

#kc_each_unfold CFSG.KD.LyA.C_4.ok 80 98 as CFSG.KD.LyA.c
  eval CFSG.KD.LyA.C_4.lo CFSG.KD.LyA.C_4.acc

end
