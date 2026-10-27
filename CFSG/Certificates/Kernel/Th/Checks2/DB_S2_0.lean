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

#kc_repo #kc_items_root CFSG.KD.ThB.S2_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S2_0_J.bin" 38043 1348072168074180355
#kc_repo #kc_items_root CFSG.KD.ThB.S2_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S2_0_lo.bin" 29 15718118940374551924
#kc_repo #kc_items_root CFSG.KD.ThB.S2_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_S2_0_acc.bin" 29 16947700502531568580

namespace CFSG.KD.ThB.S2_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runStab CFSG.KD.ThB.FB CFSG.KD.ThB.E2 (nat_lit 5) (nat_lit 1184)
      CFSG.KD.ThB.NF (nat_lit 2) CFSG.KD.ThB.SG2 (CFSG.KC.LceSeg.seg CFSG.KD.ThB.S2_0.J
      (CFSG.KD.ThB.S2_0.lo (i + 1) - CFSG.KD.ThB.S2_0.lo i) (CFSG.KD.ThB.S2_0.lo i))
      (CFSG.KD.ThB.S2_0.acc i)) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThB.S2_0.acc (i + 1))
      (Nat.succ (CFSG.KC.Th.DceS.bits CFSG.KD.ThB.MD (nat_lit 40) (nat_lit 20))) (Nat.beq i (nat_lit
      4)))

end CFSG.KD.ThB.S2_0

#kc_each_unfold CFSG.KD.ThB.S2_0.ok 0 5 as CFSG.KD.ThB.s2
  eval CFSG.KD.ThB.S2_0.lo CFSG.KD.ThB.S2_0.acc

end
