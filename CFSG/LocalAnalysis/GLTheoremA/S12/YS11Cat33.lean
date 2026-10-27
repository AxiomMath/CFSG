module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat32
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Final

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S12Cat33Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  stdCover : StdSubCoverAt G
  i173 : I173At G
  compl : Compl123At G p

section Ys11Cat33


theorem S12Cat33Inputs.toS12Cat32Inputs
    (hNLS : S265.QFactSNL) {G : Type} [Group G] [Finite G] {m p : ℕ}
    (hctx : ThmACtx G m) (hp : p ∈ Mu G m) (h : S12Cat33Inputs G p) : S12Cat32Inputs G p where
  stdCover := h.stdCover
  i265 := S265.i265StdAt_of_facts' hNLS hctx hp
  i173 := h.i173
  compl := h.compl

theorem ys11_of_cat33_inputs
    (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel) (hA : I141F.I141DynkinLie)
    (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res) (F6 : E6FourResidualFacts) (F3 : TriResidualFacts)
    (hShape : T171.T171ShapeFact) (hSize : T171.T171SizeFact) (hERank : S171.I171ExtremalRankFact)
    (hNoAct : T171.T171NoActFact) (hType : T171.T171SmallTypeFact) (hInner : T171.T171InnerU6Fact)
    (hOut : S171.I171OutDiagFact) (hU42 : S171.I171SmallIsU42Fact)
    (hA172 : S172.S172FactA) (hB172 : S172.S172FactB) (hC172 : S172.S172FactC) (hNLS : S265.QFactSNL)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat33Inputs G p) : YS11 :=
  ys11_of_cat32_inputs hR hU hA hB h155 h19 F6 F3 hShape hSize hERank hNoAct hType hInner hOut hU42 hA172 hB172 hC172
    fun G _ _ m hctx hF h11 p hp => (hin G m hctx hF h11 p hp).toS12Cat32Inputs hNLS hctx hp

end Ys11Cat33

end CFSG.LocalAnalysis.GLTheoremA
