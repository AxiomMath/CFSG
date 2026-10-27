module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DA_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThA.K_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_K_0_J.bin" 1438 12546899721754956246
#kc_repo #kc_items_root CFSG.KD.ThA.K_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_K_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThA.K_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_K_0_acc.bin" 5 16716229469519616519

namespace CFSG.KD.ThA.K_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runClass CFSG.KD.ThA.CB CFSG.KD.ThB.LT CFSG.KD.ThB.LI CFSG.KD.ThB.TL
      CFSG.KD.ThB.VL CFSG.KD.ThB.NL (CFSG.KC.LceSeg.seg CFSG.KD.ThA.K_0.J (CFSG.KD.ThA.K_0.lo (i +
      1) - CFSG.KD.ThA.K_0.lo i) (CFSG.KD.ThA.K_0.lo i)) (CFSG.KD.ThA.K_0.acc i)) (Bool.rec (motive
      := fun _ => Nat) (CFSG.KD.ThA.K_0.acc (i + 1)) (Nat.succ CFSG.KD.ThA.NCL) (Nat.beq i (nat_lit
      0)))

end CFSG.KD.ThA.K_0

#kc_each_unfold CFSG.KD.ThA.K_0.ok 0 1 as CFSG.KD.ThA.k
  eval CFSG.KD.ThA.K_0.lo CFSG.KD.ThA.K_0.acc

end
