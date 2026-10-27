module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_91.f0P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_91_0_P.bin" 147 7304381934518321141
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_91.f0I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_91_0_I.bin" 35 3525205344064885652
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_91.f1P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_91_1_P.bin" 580 647582407001183152
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_91.f1I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_91_1_I.bin" 105 11021659667921759617

namespace CFSG.KD.ThM3.Rows_M3_91

@[expose] noncomputable def f0 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_91.f0P (4 * g + 0))) (CFSG.KD.ThM3.Rows_M3_91.f0P (4 * g + 1))
    (CFSG.KD.ThM3.Rows_M3_91.f0P (4 * g + 2))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_91.f0P (4 * g
    + 3)))

@[expose] noncomputable def f1 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_91.f1P (5 * g + 0)))
    (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_91.f1P (5 * g + 1)))) (CFSG.KD.ThM3.Rows_M3_91.f1P (5 * g
    + 2)) (CFSG.KD.ThM3.Rows_M3_91.f1P (5 * g + 3))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_91.f1P
    (5 * g + 4)))

end CFSG.KD.ThM3.Rows_M3_91

#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_91.f0 7 as CFSG.KD.ThM3.cc names CFSG.KD.ThM3.Rows_M3_91.f0I
  eval CFSG.KD.ThM3.Rows_M3_91.f0P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_91.f1 21 as CFSG.KD.ThM3.cp names CFSG.KD.ThM3.Rows_M3_91.f1I
  eval CFSG.KD.ThM3.Rows_M3_91.f1P

theorem CFSG.KD.ThM3.wa : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 544))) (CFSG.KD.ThM3.RB (nat_lit 324)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.wb : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 15)) (CFSG.KD.ThM3.RB (nat_lit 545))) (CFSG.KD.ThM3.RB (nat_lit 226)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.cx1 : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KD.ThM3.RB (nat_lit 546))
    CFSG.KD.ThS.ONE) = true := by
  quickRfl

theorem CFSG.KD.ThM3.cxz : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KD.ThM3.RB (nat_lit 546))
    (CFSG.KD.ThM3.RB (nat_lit 16))) = true := by
  quickRfl

end
