module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat33
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Final
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S12Cat34Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  stdCover : StdSubCoverAt G

section Ys11Cat34


theorem inputs122_of_cat34_facts
    {G : Type} [Group G] [Finite G] {m p : ℕ} (hctx : ThmACtx G m) (hF : StageFacts G m)
    (h11 : Stage11 G m) (hp : p ∈ Mu G m) (hcov : StdSubCoverAt G) (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel)
    (hA : I141F.I141DynkinLie) (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res)
    (hShape : T171.T171ShapeFact) (hSize : T171.T171SizeFact) (hERank : S171.I171ExtremalRankFact)
    (hNoAct : T171.T171NoActFact) (hType : T171.T171SmallTypeFact) (hInner : T171.T171InnerU6Fact)
    (hOut : S171.I171OutDiagFact) (hU42 : S171.I171SmallIsU42Fact) (hNLS : S265.QFactSNL) : Inputs122 G p := by
  have hp1 : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := (S12Ctx.of_ctx hctx hF h11 hp).ctx.ctx.odd
  have hnoTri : FP.NoTrialityAt G :=
    D4T.noTrialityAt_of_autNorm D4YB.d4TwoAutNormInn_holds D4Y.noTrialityBigAt_holds
  exact ⟨⟨⟨CFSG.HardMathSupport.Solomon.Coordinator.i_7_13_1_pPrime_holds, i145UsedAt_holds G p, lBalanceEqAt_holds G p,
      input18_3_4_holds, chev2DownAt_holds (G := G) p, T171.i171one_of_facts G hShape hSize hERank hNoAct⟩,
      rank_holds G, T171.i171two_of_facts G hType hInner hOut hU42, S265.i265StdAt_of_facts' hNLS hctx hp,
      i269At_of_residual3 i269Residual3_holds G, i269SixAt_holds G, levelTwoAt_holds G,
      stdSubSmallAt_of_covers G hcov (stdSubInnerD4At_holds G), lBalanceAt_holds G p hp1⟩,
    ⟨input18_3_4_holds, i1131At_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp1 hp2,
      i1122IsoAt_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp1 hp2, chev2DownAt_holds (G := G) p,
      fieldDichotomyAt_of_noTriality hnoTri hp1 hp2, MI.autCalcAt_all G p, fieldCentIndepAt_holds G hp1 hp2,
      centTD4At_holds G, i148At_of_td4InnThreeCentLe G td4InnThreeCentLe_holds,
      I155X.i155At_of_X (i155XAt_of_res h155 G p)⟩,
    i112DiagAt_holds G, K1419.i1419_of_cases (G := G) h19.alt h19.spor h19.lie h19.cls h19.exc,
    CFSG.HardMathSupport.Dickson.BMRows.i1416TwoAt_of_sporSK
      (CFSG.HardMathSupport.Dickson.BMRows.i1416TwoSporSK_of_rows
        (CFSG.HardMathSupport.Dickson.BMRows.row_M_eleven CFSG.HardMathSupport.Dickson.BMRows.M11.centElevenBound_holds)) G,
    I141F.i141DynkinAt_of_facts hA hB G, i1429At_of_residual hR G, CatB.i102InnAt_holds G, CatB.a8CatAt_holds G,
    CatB.U42Cat.u42CatAt_of_sLevel hU G, trihalf_holds G, i91_holds G p,
    fun S _ h1 h2 => CatDistinct.field_u42_a6 CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds S h1 h2⟩

theorem S12Cat34Inputs.toS12Cat33Inputs
    (hN173 : T173.I173FactNoncyc) (hA173 : T173.I173FactA)
    (hD173 : T173.I173FactD) (hTD173 : T173.I173FactTD) (hO173 : T173.I173FactO) (hpar : T123C.ParityFact)
    (hblk : T123C.BlockFact) (h167 : T123C.I167Univ) (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel)
    (hA : I141F.I141DynkinLie) (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res)
    (hShape : T171.T171ShapeFact) (hSize : T171.T171SizeFact) (hERank : S171.I171ExtremalRankFact)
    (hNoAct : T171.T171NoActFact) (hType : T171.T171SmallTypeFact) (hInner : T171.T171InnerU6Fact)
    (hOut : S171.I171OutDiagFact) (hU42 : S171.I171SmallIsU42Fact) (hNLS : S265.QFactSNL)
    {G : Type} [Group G] [Finite G] {m p : ℕ} (hctx : ThmACtx G m) (hF : StageFacts G m) (h11 : Stage11 G m)
    (hp : p ∈ Mu G m) (h : S12Cat34Inputs G p) : S12Cat33Inputs G p where
  stdCover := h.stdCover
  i173 := T173.i173At_of_facts hN173 hA173 hD173 hTD173 hO173 G
  compl := T123C.compl123_of_facts (S12Ctx.of_ctx hctx hF h11 hp)
    (inputs122_of_cat34_facts hctx hF h11 hp h.stdCover hR hU hA hB h155 h19 hShape hSize hERank hNoAct hType hInner hOut
      hU42 hNLS) hpar hblk h167

theorem ys11_of_cat34_inputs
    (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel) (hA : I141F.I141DynkinLie)
    (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res) (F6 : E6FourResidualFacts) (F3 : TriResidualFacts)
    (hShape : T171.T171ShapeFact) (hSize : T171.T171SizeFact) (hERank : S171.I171ExtremalRankFact)
    (hNoAct : T171.T171NoActFact) (hType : T171.T171SmallTypeFact) (hInner : T171.T171InnerU6Fact)
    (hOut : S171.I171OutDiagFact) (hU42 : S171.I171SmallIsU42Fact)
    (hA172 : S172.S172FactA) (hB172 : S172.S172FactB) (hC172 : S172.S172FactC) (hNLS : S265.QFactSNL)
    (hN173 : T173.I173FactNoncyc) (hA173 : T173.I173FactA) (hD173 : T173.I173FactD)
    (hTD173 : T173.I173FactTD) (hO173 : T173.I173FactO) (hpar : T123C.ParityFact) (hblk : T123C.BlockFact)
    (h167 : T123C.I167Univ)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat34Inputs G p) : YS11 :=
  ys11_of_cat33_inputs hR hU hA hB h155 h19 F6 F3 hShape hSize hERank hNoAct hType hInner hOut hU42 hA172 hB172 hC172
    hNLS fun G _ _ m hctx hF h11 p hp =>
      (hin G m hctx hF h11 p hp).toS12Cat33Inputs hN173 hA173 hD173 hTD173 hO173 hpar hblk h167 hR hU hA hB h155 h19
        hShape hSize hERank hNoAct hType hInner hOut hU42 hNLS hctx hF h11 hp

end Ys11Cat34

end CFSG.LocalAnalysis.GLTheoremA
