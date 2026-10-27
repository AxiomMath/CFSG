module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat29
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonResidual

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys11Cat30


theorem ys11_of_cat30_inputs
    (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel) (hA : I141F.I141DynkinLie)
    (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res) (F6 : E6FourResidualFacts) (F3 : TriResidualFacts)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat29Inputs G p) : YS11 :=
  ys11_of_cat29_inputs hR hU hA hB h155 h19 fun G _ _ m hctx hF h11 p hp =>
    ⟨hin G m hctx hF h11 p hp,
      S12.canonNbrAt_of_residual_facts F6 F3 (S12Ctx.of_ctx hctx hF h11 hp) (hin G m hctx hF h11 p hp).i171one⟩

end Ys11Cat30

end CFSG.LocalAnalysis.GLTheoremA
