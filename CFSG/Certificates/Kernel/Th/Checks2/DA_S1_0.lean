module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DA_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThA.S1_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_S1_0_J.bin" 33819 9743469854285224088
#kc_repo #kc_items_root CFSG.KD.ThA.S1_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_S1_0_lo.bin" 29 15718118940374551924
#kc_repo #kc_items_root CFSG.KD.ThA.S1_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_S1_0_acc.bin" 29 16947700502531568580

namespace CFSG.KD.ThA.S1_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runStab CFSG.KD.ThA.FB CFSG.KD.ThA.E1 (nat_lit 4) (nat_lit 2336)
      CFSG.KD.ThA.NF (nat_lit 1) CFSG.KD.ThA.SG1 (CFSG.KC.LceSeg.seg CFSG.KD.ThA.S1_0.J
      (CFSG.KD.ThA.S1_0.lo (i + 1) - CFSG.KD.ThA.S1_0.lo i) (CFSG.KD.ThA.S1_0.lo i))
      (CFSG.KD.ThA.S1_0.acc i)) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThA.S1_0.acc (i + 1))
      (Nat.succ (CFSG.KC.Th.DceS.bits CFSG.KD.ThA.MD (nat_lit 20) (nat_lit 20))) (Nat.beq i (nat_lit
      4)))

end CFSG.KD.ThA.S1_0

#kc_each_unfold CFSG.KD.ThA.S1_0.ok 0 5 as CFSG.KD.ThA.s1
  eval CFSG.KD.ThA.S1_0.lo CFSG.KD.ThA.S1_0.acc

end
