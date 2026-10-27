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

#kc_repo #kc_items_root CFSG.KD.ThB.S1_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S1_0_J.bin" 101451 8291635983334214560
#kc_repo #kc_items_root CFSG.KD.ThB.S1_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S1_0_lo.bin" 69 11534919264796099462
#kc_repo #kc_items_root CFSG.KD.ThB.S1_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S1_0_acc.bin" 77 4912359698110522319

namespace CFSG.KD.ThB.S1_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runStab CFSG.KD.ThB.FB CFSG.KD.ThB.E1 (nat_lit 5) (nat_lit 1184)
      CFSG.KD.ThB.NF (nat_lit 1) CFSG.KD.ThB.SG1 (CFSG.KC.LceSeg.seg CFSG.KD.ThB.S1_0.J
      (CFSG.KD.ThB.S1_0.lo (i + 1) - CFSG.KD.ThB.S1_0.lo i) (CFSG.KD.ThB.S1_0.lo i))
      (CFSG.KD.ThB.S1_0.acc i)) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThB.S1_0.acc (i + 1))
      (Nat.succ (CFSG.KC.Th.DceS.bits CFSG.KD.ThB.MD (nat_lit 20) (nat_lit 20))) (Nat.beq i (nat_lit
      12)))

end CFSG.KD.ThB.S1_0

#kc_each_unfold CFSG.KD.ThB.S1_0.ok 0 13 as CFSG.KD.ThB.s1
  eval CFSG.KD.ThB.S1_0.lo CFSG.KD.ThB.S1_0.acc

end
