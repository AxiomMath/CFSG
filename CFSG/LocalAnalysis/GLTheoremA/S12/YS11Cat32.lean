module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat31
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S12Cat32Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  stdCover : StdSubCoverAt G
  i265 : I265StdAt G p
  i173 : I173At G
  compl : Compl123At G p

section Ys11Cat32


theorem S12Cat32Inputs.toS12Cat31Inputs
    (hA : S172.S172FactA) (hB : S172.S172FactB) (hC : S172.S172FactC)
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S12Cat32Inputs G p) : S12Cat31Inputs G p where
  stdCover := h.stdCover
  i265 := h.i265
  i173 := h.i173
  i172 :=
    S172.i172_of_facts_bridge CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hA hB hC G
  compl := h.compl

theorem ys11_of_cat32_inputs
    (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel) (hA : I141F.I141DynkinLie)
    (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res) (F6 : E6FourResidualFacts) (F3 : TriResidualFacts)
    (hShape : T171.T171ShapeFact) (hSize : T171.T171SizeFact) (hERank : S171.I171ExtremalRankFact)
    (hNoAct : T171.T171NoActFact) (hType : T171.T171SmallTypeFact) (hInner : T171.T171InnerU6Fact)
    (hOut : S171.I171OutDiagFact) (hU42 : S171.I171SmallIsU42Fact)
    (hA172 : S172.S172FactA) (hB172 : S172.S172FactB) (hC172 : S172.S172FactC)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat32Inputs G p) : YS11 :=
  ys11_of_cat31_inputs hR hU hA hB h155 h19 F6 F3 hShape hSize hERank hNoAct hType hInner hOut hU42
    fun G _ _ m hctx hF h11 p hp => (hin G m hctx hF h11 p hp).toS12Cat31Inputs hA172 hB172 hC172

end Ys11Cat32

end CFSG.LocalAnalysis.GLTheoremA
