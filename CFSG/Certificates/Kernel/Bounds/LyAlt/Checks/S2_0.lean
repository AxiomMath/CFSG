module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.S2_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S2_0_J.bin" 18159 16880237657151132239
#kc_repo #kc_items_root CFSG.KD.LyA.S2_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S2_0_lo.bin" 19 14667893835390355763
#kc_repo #kc_items_root CFSG.KD.LyA.S2_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S2_0_acc.bin" 17 13329121377246170764

namespace CFSG.KD.LyA.S2_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runStab FB E2 5 816 NF 2 SG2
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1)) (Nat.succ (bits MD 40 20)) (Nat.beq i 2))

end CFSG.KD.LyA.S2_0

#kc_each_unfold CFSG.KD.LyA.S2_0.ok 0 3 as CFSG.KD.LyA.s2
  eval CFSG.KD.LyA.S2_0.lo CFSG.KD.LyA.S2_0.acc

end
