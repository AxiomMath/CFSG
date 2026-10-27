module

public import CFSG.LocalAnalysis.GLTheoremA.Prop51Core
public import CFSG.LocalAnalysis.GLTheoremA.Prop55
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure Sec5Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  input18_3_4 : Input18_3_4
  i1131 : I1131At G p
  i1411 : I1411At G p
  i1122 : I1122At G p
  i113 : I113UsedAt G p
  i71 : I71UsedAt G p
  i2611 : I2611UsedAt G p
  i64 : I64UsedAt G p

variable {G : Type} [Group G] [Finite G]

theorem stage5_of_inputs {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    (hS3 : Stage3 G p) (hS4o : Stage4Order G p) (hS4 : Stage4 G p) (hin : Sec5Inputs G p) :
    Stage5 G p := by
  have hc := sec5Ctx_of hctx hp hS3 hS4o hS4 hin.input18_3_4
  have hrank := four_le_glaTwoLocalRank_of_mem_mu hctx hp
  have hBex := exists_glaIsBmax hc.prime.one_lt (lt_of_lt_of_le (by norm_num) hrank)
  have h51 := prop51_of hc hctx.1.charTwo (excClubHyp_of hin.i1131 hin.i1411 hin.i1122) hin.i113
  exact stage5_of hc h51
    (prop55 hc hBex hrank h51 hin.i113 P55.i336UsedAt P55.dihedralUsed hin.i71 hin.i2611 hin.i64)

theorem ys04_of_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      Sec5Inputs G p) : YS04 := by
  intro G _ _ m hctx p hp hS3 hS4o hS4
  exact stage5_of_inputs hctx hp hS3 hS4o hS4 (hin G m hctx p hp)

end CFSG.LocalAnalysis.GLTheoremA
