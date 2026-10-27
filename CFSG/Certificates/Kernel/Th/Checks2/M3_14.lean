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

#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f0P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_0_P.bin" 44 7175615936571769230
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f0I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_0_I.bin" 19 14667893835390355763
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f1P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_1_P.bin" 84 7032578528703788568
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f1I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_1_I.bin" 19 14667893835390355763
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_2_P.bin" 268 7964728300812622037
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_2_I.bin" 60 14398628932478830034
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f3P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_3_P.bin" 110 18179874903448799394
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f3I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_3_I.bin" 19 14667893835390355763
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f4P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_4_P.bin" 64 2562389971225712024
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f4I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_4_I.bin" 15 1394112397386276422
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f5P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_5_P.bin" 206 17068185354696491625
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_14.f5I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_14_5_I.bin" 45 13171427986030984090

namespace CFSG.KD.ThM3.Rows_M3_14

@[expose] noncomputable def f0 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f0P (2 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f0P (2 * g
    + 1)))) CFSG.KD.ThS.ONE

@[expose] noncomputable def f1 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f1P (4 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f1P (4 * g
    + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f1P (4 * g + 2))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f1P (4 * g
    + 3))))

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f2P (4 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f2P (4 * g
    + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f2P (4 * g + 2))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f2P (4 * g
    + 3))))

@[expose] noncomputable def f3 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f3P (5 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f3P (5 * g
    + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f3P (5 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f3P (5 * g + 3)))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f3P (5 * g
    + 4))))

@[expose] noncomputable def f4 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f4P (4 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f4P (4 * g
    + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f4P (4 * g + 2))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f4P (4 * g
    + 3))))

@[expose] noncomputable def f5 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f5P (4 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f5P (4 * g
    + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_14.f5P (4 * g + 2))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_14.f5P (4 * g
    + 3))))

end CFSG.KD.ThM3.Rows_M3_14

#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_14.f0 4 as CFSG.KD.ThM3.ee names CFSG.KD.ThM3.Rows_M3_14.f0I
  eval CFSG.KD.ThM3.Rows_M3_14.f0P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_14.f1 4 as CFSG.KD.ThM3.ec0 names CFSG.KD.ThM3.Rows_M3_14.f1I
  eval CFSG.KD.ThM3.Rows_M3_14.f1P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_14.f2 12 as CFSG.KD.ThM3.ec names CFSG.KD.ThM3.Rows_M3_14.f2I
  eval CFSG.KD.ThM3.Rows_M3_14.f2P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_14.f3 4 as CFSG.KD.ThM3.fe names CFSG.KD.ThM3.Rows_M3_14.f3I
  eval CFSG.KD.ThM3.Rows_M3_14.f3P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_14.f4 3 as CFSG.KD.ThM3.fc0 names CFSG.KD.ThM3.Rows_M3_14.f4I
  eval CFSG.KD.ThM3.Rows_M3_14.f4P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_14.f5 9 as CFSG.KD.ThM3.fc names CFSG.KD.ThM3.Rows_M3_14.f5I
  eval CFSG.KD.ThM3.Rows_M3_14.f5P

end
