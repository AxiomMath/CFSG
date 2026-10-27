module

public import CFSG.GH74.Generic.BProg.B3.S3HLO
public import CFSG.GH74.Generic.BProg.B3.S3Rk4Final
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Prop312Final
public import CFSG.GH74.Generic.BProg.B3.RankC

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Group G] [Finite G] in
theorem stage1BalFor_shape3_of_c2' (hC2 : C2CoverInput) (hNo : B2.NoJPrimeNonSD)
    (hSD29 : ∀ {G : Type} [Group G] [Finite G] {x a : G} {K A D J : Subgroup G},
      Ctx21 G x K A a D J → B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → pRank 2 ↥(CxK x K) ≤ 1) :
    Stage1BalFor QShape3 := by
  refine stage1BalFor_of_ctx fun G _ _ x K A a D J hc hP => ?_
  have h306 : Prop306aBarAt x K A := prop306aBarAt_of_inputs hC2 fun _ h => hLO_proved hC2 h
  rcases B1.qShape3_split hP with hW | hSD
  · exact false_of_ctx_s3_rank1 h306 hc hP (Ctx21.pRank_cxk_le_one hNo hc (Or.inr (Or.inl hW)))
  · exact false_of_ctx_s3_rank1 h306 hc hP (hSD29 hc hSD)

end CFSG.GH74.Generic.BProg.B3
