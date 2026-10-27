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

#kc_repo #kc_items_root CFSG.KD.ThA.C_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_0_J.bin" 10560 4539672441773419107
#kc_repo #kc_items_root CFSG.KD.ThA.C_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_0_lo.bin" 54 6718073966312452302
#kc_repo #kc_items_root CFSG.KD.ThA.C_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_0_acc.bin" 65 17863107131694187711

namespace CFSG.KD.ThA.C_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runCover CFSG.KD.ThA.FB CFSG.KD.ThA.OB (nat_lit 4) (nat_lit 2336)
      CFSG.KD.ThA.osh CFSG.KD.ThA.owd CFSG.KD.ThA.om CFSG.KD.ThA.NB CFSG.KD.ThA.sel CFSG.KD.ThA.NF
      CFSG.KD.ThA.NO CFSG.KD.ThA.AL (CFSG.KC.LceSeg.seg CFSG.KD.ThA.C_0.J (CFSG.KD.ThA.C_0.lo (i +
      1) - CFSG.KD.ThA.C_0.lo i) (CFSG.KD.ThA.C_0.lo i)) (CFSG.KD.ThA.C_0.acc i))
      (CFSG.KD.ThA.C_0.acc (i + 1))

end CFSG.KD.ThA.C_0

#kc_each_unfold CFSG.KD.ThA.C_0.ok 0 10 as CFSG.KD.ThA.c
  eval CFSG.KD.ThA.C_0.lo CFSG.KD.ThA.C_0.acc

end
