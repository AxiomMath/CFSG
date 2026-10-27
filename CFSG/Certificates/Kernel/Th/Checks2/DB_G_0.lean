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

#kc_repo #kc_items_root CFSG.KD.ThB.G_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_G_0_J.bin" 54 6563793261085730062
#kc_repo #kc_items_root CFSG.KD.ThB.G_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_G_0_lo.bin" 49 13319687021087572164
#kc_repo #kc_items_root CFSG.KD.ThB.G_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_G_0_acc.bin" 53 16767764364639547243

namespace CFSG.KD.ThB.G_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runGom CFSG.KD.ThB.HB CFSG.KD.ThB.GB CFSG.KD.ThB.OB CFSG.KD.ThB.osh
      CFSG.KD.ThB.owd CFSG.KD.ThB.om CFSG.KD.ThB.NB CFSG.KD.ThB.sel CFSG.KD.ThB.I0 CFSG.KD.ThB.nH
      (CFSG.KC.LceSeg.seg CFSG.KD.ThB.G_0.J (CFSG.KD.ThB.G_0.lo (i + 1) - CFSG.KD.ThB.G_0.lo i)
      (CFSG.KD.ThB.G_0.lo i)) (CFSG.KD.ThB.G_0.acc i)) (Bool.rec (motive := fun _ => Nat)
      (CFSG.KD.ThB.G_0.acc (i + 1)) (Nat.succ CFSG.KD.ThB.NO) (Nat.beq i (nat_lit 8)))

end CFSG.KD.ThB.G_0

#kc_each_unfold CFSG.KD.ThB.G_0.ok 0 9 as CFSG.KD.ThB.g
  eval CFSG.KD.ThB.G_0.lo CFSG.KD.ThB.G_0.acc

end
