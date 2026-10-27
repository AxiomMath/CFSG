module

import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.HOrb
import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.M
import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels
import CFSG.Certificates.Kernel.Bounds.HSAlt.Pair

#kc_repo #kc_items_root CFSG.KD.HSKM.MRows.P0 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/M/rows/M_0_P.bin" 1217 2108006909280231382
#kc_repo #kc_items_root CFSG.KD.HSKM.MRows.P1 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/M/rows/M_1_P.bin" 299 9302478412466804036
#kc_repo #kc_items_root CFSG.KD.HSKM.MRows.P2 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/M/rows/M_2_P.bin" 150 2316961158171672513
#kc_repo #kc_items_root CFSG.KD.HSKM.MRows.P3 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/M/rows/M_3_P.bin" 299 5130079899134197131

namespace CFSG.KD.HSKM.MRows

open CFSG.KD.HSKM CFSG.KC

noncomputable def par (g : Nat) : Bool :=
  Nat.beq (Nat.land (LceS.wLen (XRs (P0 (3 * g + 0)))) (P0 (3 * g + 1))) (P0 (3 * g + 2))

noncomputable def gw (g : Nat) : Bool :=
  Nat.beq (HSK.gen (P1 (2 * g + 0))) (GWs (P1 (2 * g + 1)))

noncomputable def conj (g : Nat) : Bool :=
  HSK.conjOK (HSK.gen (P2 g))

noncomputable def sub (g : Nat) : Bool :=
  Nat.beq (HSK.subS (P3 (2 * g + 0))) (HSK.gen (P3 (2 * g + 1)))

noncomputable def root1 (_ : Nat) : Bool := Nat.beq (HOrb.commPow HSK.U1 5) (HSK.rel 4)

noncomputable def root2 (_ : Nat) : Bool := Nat.beq (HOrb.commPow HSK.U2 3) (HSK.rel 5)

noncomputable def root3 (_ : Nat) : Bool := Nat.beq (HOrb.commPow HSK.U3 6) (HSK.rel 6)

noncomputable def rexp (_ : Nat) : Bool :=
  Nat.beq (Nat.add (Nat.mul (HSK.rootExp 1) (nat_lit 1000)) (Nat.add (Nat.mul (HSK.rootExp 2)
    (nat_lit 100)) (Nat.add (Nat.mul (HSK.rootExp 3) (nat_lit 10)) (HSK.rootExp 4)))) (nat_lit 5362)

noncomputable def u4 (_ : Nat) : Bool := Nat.beq HSK.U4 (nat_lit 0x202000303000202020)

end CFSG.KD.HSKM.MRows

#kc_each_unfold CFSG.KD.HSKM.MRows.par 0 87 as CFSG.KD.HSKM.par eval CFSG.KD.HSKM.MRows.P0
#kc_each_unfold CFSG.KD.HSKM.MRows.gw 1 31 as CFSG.KD.HSKM.gw at 0 eval CFSG.KD.HSKM.MRows.P1
#kc_each_unfold CFSG.KD.HSKM.MRows.conj 1 31 as CFSG.KD.HSKM.conj at 0 eval CFSG.KD.HSKM.MRows.P2
#kc_each_unfold CFSG.KD.HSKM.MRows.sub 0 30 as CFSG.KD.HSKM.sub eval CFSG.KD.HSKM.MRows.P3
#kc_unfold CFSG.KD.HSKM.root1 CFSG.KD.HSKM.MRows.root1 0
#kc_unfold CFSG.KD.HSKM.root2 CFSG.KD.HSKM.MRows.root2 0
#kc_unfold CFSG.KD.HSKM.root3 CFSG.KD.HSKM.MRows.root3 0
#kc_unfold CFSG.KD.HSKM.rexp CFSG.KD.HSKM.MRows.rexp 0
#kc_unfold CFSG.KD.HSKM.u4 CFSG.KD.HSKM.MRows.u4 0
