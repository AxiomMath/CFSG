module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat27
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KCanonRank3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys11Cat28


theorem ys11_of_cat28_inputs
    (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel) (hA : I141F.I141DynkinLie)
    (hB : I141F.I141RankSmall) (h155 : I155XRes)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat27Inputs G p ∧ S12.CanonNbrAt G p) : YS11 :=
  ys11_of_cat27_inputs hR hU hA hB h155 fun G _ _ m hctx hF h11 p hp =>
    ⟨(hin G m hctx hF h11 p hp).1, ⟨rank3_holds G, (hin G m hctx hF h11 p hp).2⟩⟩

end Ys11Cat28

end CFSG.LocalAnalysis.GLTheoremA
