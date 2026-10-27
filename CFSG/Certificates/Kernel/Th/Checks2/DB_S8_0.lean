module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThB.S8_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S8_0_J.bin" 218 15897705679394276069
#kc_repo #kc_items_root CFSG.KD.ThB.S8_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S8_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThB.S8_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S8_0_acc.bin" 5 16716229469519616519

namespace CFSG.KD.ThB.S8_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runStab CFSG.KD.ThB.FB CFSG.KD.ThB.E8 (nat_lit 5) (nat_lit 1184)
      CFSG.KD.ThB.NF (nat_lit 8) CFSG.KD.ThB.SG8 (CFSG.KC.LceSeg.seg CFSG.KD.ThB.S8_0.J
      (CFSG.KD.ThB.S8_0.lo (i + 1) - CFSG.KD.ThB.S8_0.lo i) (CFSG.KD.ThB.S8_0.lo i))
      (CFSG.KD.ThB.S8_0.acc i)) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThB.S8_0.acc (i + 1))
      (Nat.succ (CFSG.KC.Th.DceS.bits CFSG.KD.ThB.MD (nat_lit 160) (nat_lit 20))) (Nat.beq i
      (nat_lit 0)))

end CFSG.KD.ThB.S8_0

#kc_each_unfold CFSG.KD.ThB.S8_0.ok 0 1 as CFSG.KD.ThB.s8
  eval CFSG.KD.ThB.S8_0.lo CFSG.KD.ThB.S8_0.acc

end
