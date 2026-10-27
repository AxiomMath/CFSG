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

#kc_repo #kc_items_root CFSG.KD.ThA.G_1.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_1_J.bin" 252060 14657229012576617000
#kc_repo #kc_items_root CFSG.KD.ThA.G_1.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_1_lo.bin" 54 6718073966312452302
#kc_repo #kc_items_root CFSG.KD.ThA.G_1.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_1_acc.bin" 66 8856870940213219924

namespace CFSG.KD.ThA.G_1

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runGom CFSG.KD.ThA.HB CFSG.KD.ThA.GB CFSG.KD.ThA.OB CFSG.KD.ThA.osh
      CFSG.KD.ThA.owd CFSG.KD.ThA.om CFSG.KD.ThA.NB CFSG.KD.ThA.sel CFSG.KD.ThA.I0 CFSG.KD.ThA.nH
      (CFSG.KC.LceSeg.seg CFSG.KD.ThA.G_1.J (CFSG.KD.ThA.G_1.lo (i + 1 - 10) - CFSG.KD.ThA.G_1.lo (i
      - 10)) (CFSG.KD.ThA.G_1.lo (i - 10))) (CFSG.KD.ThA.G_1.acc (i - 10))) (CFSG.KD.ThA.G_1.acc (i
      + 1 - 10))

end CFSG.KD.ThA.G_1

#kc_each_unfold CFSG.KD.ThA.G_1.ok 10 20 as CFSG.KD.ThA.g
  eval CFSG.KD.ThA.G_1.lo CFSG.KD.ThA.G_1.acc

end
