module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Red
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PAmbig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PRedSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PDiagIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PLinTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PLinNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PUniNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PSympTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PSympNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthPlusNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthMinusNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PSympDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthPlusDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthMinusDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PDiagBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PCompAction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PTriNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PTriDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcUNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcUDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PTwE6Norm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PTwE6Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PSuzTits
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PLinDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PUniDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PReeNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PReeDiag
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.LocalAnalysis.GLTheoremA.I171


theorem i171ShapeFact15_of_residuals (hK : T171Sh.ExcKernelCompAction) (hD4U : ExcAdjD4Inner)
    (hD4T : TwE6D4Inner) : I171ShapeFact15 := by
  have hTr : MarkTransport := markTransport_holds
  have hOut : OutHalf := outHalf_holds
  have hL : CatLayer := catLayer_holds
  have hC : CatChevComps := catChevComps_holds
  have hB : DiagOfBlock := diagOfBlock_holds
  have hG : DiagOfCompAction := diagOfCompAction_holds
  have hNI : ShapeModelNormIso := shapeModelNormIso_holds
  have hDI : ShapeModelDiagIso := shapeModelDiagIso_holds
  have hIso : ShapeModelIso := shapeModelIso_holds
  have hA : T171Sh.ExcAdjCompInnAut :=
    T171Sh.excAdjCompInnAut_of hK T171Sh.e6CentralizerConnOddExcKernels_holds
  exact i171ShapeFact15_of_halves hOut ambigHalf_holds
    (redSimpleNorm_holds _ hOut (linNormTrans_holds hNI linNormModel_holds)) linDiag_holds
    (redSimpleNorm_holds _ hOut (uniNormTrans_holds hNI uniNormModel_holds)) uniDiag_holds
    (redSimple_holds hTr _ hOut (sympTrans_holds hIso
      (sympModel_of_halves sympNorm_holds
        (sympDiag_of_block hL hC hB hTr hDI T171Sh.sympComponentBlockAnalysis_holds))))
    (redSimple_holds hTr _ hOut (orthModelTrans_holds hIso
      (orthPlusModel_of_halves orthPlusNorm_holds (orthPlusDiag_of_block hL hC hB hTr hDI
        T171Sh.orthComponentBlockAnalysisPlus_holds))
      (orthMinusModel_of_halves orthMinusNorm_holds
        (orthMinusDiag_of_block hL hC hB hTr hDI
          T171Sh.orthComponentBlockAnalysisMinus_holds))))
    (redSimple_holds hTr _ hOut
      (simpleModel_of_halves (triNorm_of hL hNI) (triDiag_of_block hL hC hB hTr hDI)))
    (redSimple_holds hTr _ hOut
      (simpleModel_of_halves (excUNorm_of hL hNI) (excUDiag_of hA hD4U hL hC hG hTr hDI)))
    (redSimple_holds hTr _ hOut (simpleModel_excT
      (simpleModel_of_halves (twE6Norm_of hL hNI) (twE6Diag_of hK hD4T hL hC hG hTr hDI))
      (simpleModel_of_halves (reeF4Norm_of hL) reeF4Diag_holds) simpleModel_suzTits_holds))

end CFSG.LocalAnalysis.GLTheoremA.F151

end
