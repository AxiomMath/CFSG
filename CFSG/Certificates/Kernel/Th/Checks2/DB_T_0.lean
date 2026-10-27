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

#kc_repo #kc_items_root CFSG.KD.ThB.T_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_T_0_J.bin" 272026 11476772613468862001
#kc_repo #kc_items_root CFSG.KD.ThB.T_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_T_0_lo.bin" 129 18297413468952889920
#kc_repo #kc_items_root CFSG.KD.ThB.T_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_T_0_acc.bin" 149 6779446492575437969

namespace CFSG.KD.ThB.T_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runT CFSG.KD.ThB.HB CFSG.KD.ThB.TB CFSG.KD.ThB.OB CFSG.KD.ThB.RR
      CFSG.KD.ThA.FB CFSG.KD.ThB.LT CFSG.KD.ThB.TL CFSG.KD.ThB.VL CFSG.KD.ThB.NL CFSG.KD.ThB.NR
      CFSG.KD.ThB.nH CFSG.KD.ThB.nT CFSG.KD.ThB.osh CFSG.KD.ThB.owd CFSG.KD.ThB.om CFSG.KD.ThB.NB
      CFSG.KD.ThB.sel CFSG.KD.ThB.I0 (nat_lit 4) (nat_lit 2336) CFSG.KD.ThA.NF (CFSG.KC.LceSeg.seg
      CFSG.KD.ThB.T_0.J (CFSG.KD.ThB.T_0.lo (i + 1) - CFSG.KD.ThB.T_0.lo i) (CFSG.KD.ThB.T_0.lo i))
      (CFSG.KD.ThB.T_0.acc i)) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThB.T_0.acc (i + 1))
      (Nat.succ CFSG.KD.ThB.nT) (Nat.beq i (nat_lit 24)))

end CFSG.KD.ThB.T_0

#kc_each_unfold CFSG.KD.ThB.T_0.ok 0 25 as CFSG.KD.ThB.t
  eval CFSG.KD.ThB.T_0.lo CFSG.KD.ThB.T_0.acc

end
