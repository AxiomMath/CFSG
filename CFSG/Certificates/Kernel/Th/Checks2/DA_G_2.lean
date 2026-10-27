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

#kc_repo #kc_items_root CFSG.KD.ThA.G_2.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_2_J.bin" 173418 15992289278781833502
#kc_repo #kc_items_root CFSG.KD.ThA.G_2.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_2_lo.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.ThA.G_2.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_2_acc.bin" 42 12242507557364739209

namespace CFSG.KD.ThA.G_2

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runGom CFSG.KD.ThA.HB CFSG.KD.ThA.GB CFSG.KD.ThA.OB CFSG.KD.ThA.osh
      CFSG.KD.ThA.owd CFSG.KD.ThA.om CFSG.KD.ThA.NB CFSG.KD.ThA.sel CFSG.KD.ThA.I0 CFSG.KD.ThA.nH
      (CFSG.KC.LceSeg.seg CFSG.KD.ThA.G_2.J (CFSG.KD.ThA.G_2.lo (i + 1 - 20) - CFSG.KD.ThA.G_2.lo (i
      - 20)) (CFSG.KD.ThA.G_2.lo (i - 20))) (CFSG.KD.ThA.G_2.acc (i - 20))) (Bool.rec (motive := fun
      _ => Nat) (CFSG.KD.ThA.G_2.acc (i + 1 - 20)) (Nat.succ CFSG.KD.ThA.NO) (Nat.beq i (nat_lit
      26)))

end CFSG.KD.ThA.G_2

#kc_each_unfold CFSG.KD.ThA.G_2.ok 20 27 as CFSG.KD.ThA.g
  eval CFSG.KD.ThA.G_2.lo CFSG.KD.ThA.G_2.acc

end
