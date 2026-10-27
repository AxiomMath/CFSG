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

#kc_repo #kc_items_root CFSG.KD.ThA.G_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_0_J.bin" 252060 9117598091528903481
#kc_repo #kc_items_root CFSG.KD.ThA.G_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_0_lo.bin" 54 6718073966312452302
#kc_repo #kc_items_root CFSG.KD.ThA.G_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_G_0_acc.bin" 65 9517424403620750742

namespace CFSG.KD.ThA.G_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runGom CFSG.KD.ThA.HB CFSG.KD.ThA.GB CFSG.KD.ThA.OB CFSG.KD.ThA.osh
      CFSG.KD.ThA.owd CFSG.KD.ThA.om CFSG.KD.ThA.NB CFSG.KD.ThA.sel CFSG.KD.ThA.I0 CFSG.KD.ThA.nH
      (CFSG.KC.LceSeg.seg CFSG.KD.ThA.G_0.J (CFSG.KD.ThA.G_0.lo (i + 1) - CFSG.KD.ThA.G_0.lo i)
      (CFSG.KD.ThA.G_0.lo i)) (CFSG.KD.ThA.G_0.acc i)) (CFSG.KD.ThA.G_0.acc (i + 1))

end CFSG.KD.ThA.G_0

#kc_each_unfold CFSG.KD.ThA.G_0.ok 0 10 as CFSG.KD.ThA.g
  eval CFSG.KD.ThA.G_0.lo CFSG.KD.ThA.G_0.acc

end
