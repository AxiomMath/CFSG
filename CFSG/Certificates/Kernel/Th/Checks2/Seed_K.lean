module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThSeed.Rows_Seed_K.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Seed_K_2_P.bin" 35 9880560866738996884
#kc_repo #kc_items_root CFSG.KD.ThSeed.Rows_Seed_K.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Seed_K_2_I.bin" 5 16058875513670357405
#kc_repo #kc_items_root CFSG.KD.ThSeed.Rows_Seed_K.f3P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Seed_K_3_P.bin" 35 10889480281175795768
#kc_repo #kc_items_root CFSG.KD.ThSeed.Rows_Seed_K.f3I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Seed_K_3_I.bin" 5 16716229469519616519

namespace CFSG.KD.ThSeed.Rows_Seed_K

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq CFSG.KD.ThS.w1 (CFSG.KD.ThSeed.Rows_Seed_K.f2P (1 * g + 0))

@[expose] noncomputable def f3 (g : Nat) : Bool :=
  Nat.beq CFSG.KD.ThS.w2 (CFSG.KD.ThSeed.Rows_Seed_K.f3P (1 * g + 0))

end CFSG.KD.ThSeed.Rows_Seed_K

#kc_rows_unfold CFSG.KD.ThSeed.Rows_Seed_K.f2 1 as CFSG.KD.ThSeed.kW names
  CFSG.KD.ThSeed.Rows_Seed_K.f2I eval CFSG.KD.ThSeed.Rows_Seed_K.f2P
#kc_rows_unfold CFSG.KD.ThSeed.Rows_Seed_K.f3 1 as CFSG.KD.ThSeed.kW names
  CFSG.KD.ThSeed.Rows_Seed_K.f3I eval CFSG.KD.ThSeed.Rows_Seed_K.f3P

theorem CFSG.KD.ThSeed.kA : Nat.beq (CFSG.KD.ThS.RBf (nat_lit 1)) CFSG.KD.ThSeed.SA = true := by
  quickRfl

theorem CFSG.KD.ThSeed.kB : Nat.beq (CFSG.KD.ThS.RBf (nat_lit 2)) CFSG.KD.ThSeed.SB = true := by
  quickRfl

end
