module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat34
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys11Cat35


theorem ys11_of_cat35_inputs
    (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel) (hA : I141F.I141DynkinLie)
    (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res) (F6 : E6FourResidualFacts) (F3 : TriResidualFacts)
    (hShape : T171.T171ShapeFact) (hSize : T171.T171SizeFact) (hERank : S171.I171ExtremalRankFact)
    (hNoAct : T171.T171NoActFact) (hType : T171.T171SmallTypeFact) (hInner : T171.T171InnerU6Fact)
    (hOut : S171.I171OutDiagFact) (hU42 : S171.I171SmallIsU42Fact)
    (hA172 : S172.S172FactA) (hB172 : S172.S172FactB) (hC172 : S172.S172FactC) (hNLS : S265.QFactSNL)
    (hN173 : T173.I173FactNoncyc) (hA173 : T173.I173FactA) (hD173 : T173.I173FactD)
    (hTD173 : T173.I173FactTD) (hO173 : T173.I173FactO) (hpar : T123C.ParityFact) (hblk : T123C.BlockFact)
    (h167 : T123C.I167Univ)
    (hS : StdCovSchurAt) (hL : StdCovListAt) (hC : StdCovDiagCentreAt) (hO : StdCovDiagOddAt)
    (hE : StdCovDiagExclAt) : YS11 :=
  ys11_of_cat34_inputs hR hU hA hB h155 h19 F6 F3 hShape hSize hERank hNoAct hType hInner hOut hU42 hA172 hB172
    hC172 hNLS hN173 hA173 hD173 hTD173 hO173 hpar hblk h167
    fun G _ _ _ _ _ _ _ _ => ⟨stdSubCoverAt_of_diag_facts G hS hL hC hO hE⟩

end Ys11Cat35

end CFSG.LocalAnalysis.GLTheoremA
