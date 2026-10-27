module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat23
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL10

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys05Cat24


theorem ys05_of_cat24_inputs
    (hR : D3A4Regular) (hN : D3CaseTwoOne)
    (hRes : I264bResidual2) (hS1 : I1422Lie2Fact) (h17 : I2017LRes) (h20 : I2020Res) (h248 : I248Res) (h81 : I81Res)
    (h196 : I196Res)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S6Cat23Inputs G p) : YS05 :=
  ys05_of_cat16_inputs
    (CFSG.HardMathSupport.Dickson.BMRows.qrow_M_eleven CFSG.HardMathSupport.Dickson.BMRows.M11.centElevenBound_holds)
    ⟨d3InnerInvolution_of_sylow (d3InnerSylow_of_levi d3InnerLevi_holds), d3FieldInvolution_holds,
      d3FixedPointFree_of_regular (d3InnerInvolution_of_sylow (d3InnerSylow_of_levi d3InnerLevi_holds))
        d3FieldInvolution_holds hR hN⟩
    fun G _ _ m hctx p hp =>
      ((((h G m hctx p hp).toS6Cat22Inputs h81 h196).toS6Cat21Inputs h17 h20 h248).toS6Cat17Inputs hS1).toS6Cat14Inputs
        (i264bResidual_of_2 hRes)

end Ys05Cat24

end CFSG.LocalAnalysis.GLTheoremA
