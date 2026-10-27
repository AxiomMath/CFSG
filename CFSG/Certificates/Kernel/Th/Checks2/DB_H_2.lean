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

#kc_repo #kc_items_root CFSG.KD.ThB.H_2.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_2_J.bin" 151838 7920215814291739793
#kc_repo #kc_items_root CFSG.KD.ThB.H_2.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_2_lo.bin" 79 942806023431972370
#kc_repo #kc_items_root CFSG.KD.ThB.H_2.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_H_2_acc.bin" 105 17397875008715237360

namespace CFSG.KD.ThB.H_2

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runHdr CFSG.KD.ThB.HB CFSG.KD.ThA.FB CFSG.KD.ThB.LT CFSG.KD.ThB.TL
      CFSG.KD.ThB.VL CFSG.KD.ThB.NL (nat_lit 4) (nat_lit 2336) CFSG.KD.ThA.NF (CFSG.KC.LceSeg.seg
      CFSG.KD.ThB.H_2.J (CFSG.KD.ThB.H_2.lo (i + 1 - 40) - CFSG.KD.ThB.H_2.lo (i - 40))
      (CFSG.KD.ThB.H_2.lo (i - 40))) (CFSG.KD.ThB.H_2.acc (i - 40))) (Bool.rec (motive := fun _ =>
      Nat) (CFSG.KD.ThB.H_2.acc (i + 1 - 40)) (Nat.succ CFSG.KD.ThB.nH) (Nat.beq i (nat_lit 54)))

end CFSG.KD.ThB.H_2

#kc_each_unfold CFSG.KD.ThB.H_2.ok 40 55 as CFSG.KD.ThB.h
  eval CFSG.KD.ThB.H_2.lo CFSG.KD.ThB.H_2.acc

end
