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

#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_90.f1P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_90_1_P.bin" 199 7185422129176829487
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_90.f1I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_90_1_I.bin" 29 199695477374880050

namespace CFSG.KD.ThM3.Rows_M3_90

@[expose] noncomputable def f1 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_90.f1P (6 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_90.f1P (6 * g
    + 1))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_90.f1P (6 * g + 2))) (CFSG.KD.ThM3.Rows_M3_90.f1P
    (6 * g + 3)) (CFSG.KD.ThM3.Rows_M3_90.f1P (6 * g + 4))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_90.f1P (6 * g + 5))) CFSG.KD.ThS.ONE)

end CFSG.KD.ThM3.Rows_M3_90

#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_90.f1 6 as CFSG.KD.ThM3.pq names CFSG.KD.ThM3.Rows_M3_90.f1I
  eval CFSG.KD.ThM3.Rows_M3_90.f1P

theorem CFSG.KD.ThM3.pz : Nat.beq (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB
    (nat_lit 15)) (nat_lit 1352160579797152663358438253090) (nat_lit 52)) (CFSG.KD.ThM3.RB (nat_lit
    16)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.pq3 : Nat.beq (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB
    (nat_lit 15)) (nat_lit 340018248) (nat_lit 16)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KD.ThM3.RB (nat_lit 20)) (CFSG.KD.ThM3.RB (nat_lit 16))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.pq7 : Nat.beq (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB
    (nat_lit 15)) (nat_lit 74159768712) (nat_lit 20)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KD.ThM3.RB (nat_lit 24)) (CFSG.KD.ThM3.RB (nat_lit 16))) = true := by
  quickRfl

end
