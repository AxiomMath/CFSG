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

#kc_repo #kc_items_root CFSG.KD.ThA.C_6.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_6_J.bin" 510 4408309969280352689
#kc_repo #kc_items_root CFSG.KD.ThA.C_6.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_6_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThA.C_6.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_C_6_acc.bin" 7 7561605424849590220

namespace CFSG.KD.ThA.C_6

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runCover CFSG.KD.ThA.FB CFSG.KD.ThA.OB (nat_lit 4) (nat_lit 2336)
      CFSG.KD.ThA.osh CFSG.KD.ThA.owd CFSG.KD.ThA.om CFSG.KD.ThA.NB CFSG.KD.ThA.sel CFSG.KD.ThA.NF
      CFSG.KD.ThA.NO CFSG.KD.ThA.AL (CFSG.KC.LceSeg.seg CFSG.KD.ThA.C_6.J (CFSG.KD.ThA.C_6.lo (i + 1
      - 60) - CFSG.KD.ThA.C_6.lo (i - 60)) (CFSG.KD.ThA.C_6.lo (i - 60))) (CFSG.KD.ThA.C_6.acc (i -
      60))) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThA.C_6.acc (i + 1 - 60)) (Nat.add (nat_lit
      1) (Nat.shiftLeft CFSG.KD.ThA.ND (nat_lit 20))) (Nat.beq i (nat_lit 60)))

end CFSG.KD.ThA.C_6

#kc_each_unfold CFSG.KD.ThA.C_6.ok 60 61 as CFSG.KD.ThA.c
  eval CFSG.KD.ThA.C_6.lo CFSG.KD.ThA.C_6.acc

end
