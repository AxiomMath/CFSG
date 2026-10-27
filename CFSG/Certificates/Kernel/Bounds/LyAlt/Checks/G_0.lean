module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.G_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/G_0_J.bin" 73476 3949898618935127067
#kc_repo #kc_items_root CFSG.KD.LyA.G_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/G_0_lo.bin" 204 15656457655126758369
#kc_repo #kc_items_root CFSG.KD.LyA.G_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/G_0_acc.bin" 239 5846318507933576256

namespace CFSG.KD.LyA.G_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runGom HB GB OB I0 nH
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1)) (Nat.succ NO) (Nat.beq i 39))

end CFSG.KD.LyA.G_0

#kc_each_unfold CFSG.KD.LyA.G_0.ok 0 40 as CFSG.KD.LyA.g
  eval CFSG.KD.LyA.G_0.lo CFSG.KD.LyA.G_0.acc

end
