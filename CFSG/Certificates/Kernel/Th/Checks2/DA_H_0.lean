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

#kc_repo #kc_items_root CFSG.KD.ThA.H_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_H_0_J.bin" 87955 129513227508592801
#kc_repo #kc_items_root CFSG.KD.ThA.H_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_H_0_lo.bin" 49 14692733499740050738
#kc_repo #kc_items_root CFSG.KD.ThA.H_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_H_0_acc.bin" 53 16767764364639547243

namespace CFSG.KD.ThA.H_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runHdr CFSG.KD.ThA.HB CFSG.KD.ThA.FB CFSG.KD.ThA.LT CFSG.KD.ThA.TL
      CFSG.KD.ThA.VL CFSG.KD.ThA.NL (nat_lit 4) (nat_lit 2336) (nat_lit 0) (CFSG.KC.LceSeg.seg
      CFSG.KD.ThA.H_0.J (CFSG.KD.ThA.H_0.lo (i + 1) - CFSG.KD.ThA.H_0.lo i) (CFSG.KD.ThA.H_0.lo i))
      (CFSG.KD.ThA.H_0.acc i)) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThA.H_0.acc (i + 1))
      (Nat.succ CFSG.KD.ThA.nH) (Nat.beq i (nat_lit 8)))

end CFSG.KD.ThA.H_0

#kc_each_unfold CFSG.KD.ThA.H_0.ok 0 9 as CFSG.KD.ThA.h
  eval CFSG.KD.ThA.H_0.lo CFSG.KD.ThA.H_0.acc

end
