module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.H_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/H_0_J.bin" 212015 7812472572305613723
#kc_repo #kc_items_root CFSG.KD.LyA.H_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/H_0_lo.bin" 104 12762208272718576803
#kc_repo #kc_items_root CFSG.KD.LyA.H_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/H_0_acc.bin" 119 7969713170498518176

namespace CFSG.KD.LyA.H_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runHdr HB LT TL VL NL
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1)) (Nat.succ nH) (Nat.beq i 19))

end CFSG.KD.LyA.H_0

#kc_each_unfold CFSG.KD.LyA.H_0.ok 0 20 as CFSG.KD.LyA.h
  eval CFSG.KD.LyA.H_0.lo CFSG.KD.LyA.H_0.acc

end
