module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A7
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Sp44Case
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NotStandard
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GoldMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HResidual
public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Top

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child4_of_frontier
    (hCatZ2A6 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)))
    (hA6A6 : M22Std.Prop21A6A6Case)
    (hCatZ2A7 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 7)))
    (hHypA : M24Std.Ega81HypAZ2A8K)
    (hHarrisSolomon : M24Std.HarrisSolomonZ2S6IsoK) :
    M22M23M24Exclusion := by
  intro G _ _ L h
  have hSolZ2A6 := SolomonRed.solomonZ2A6_of_cat hCatZ2A6
  have hSolZ2A7 := SolomonRed.solomonZ2A7_of_cat hCatZ2A7
  have h25 := Finkelstein77.Lemma25HProof.asc76Lemma25_of_hallQ8Residual
    ComponentClassification.Foote5.HallGen.hallQ8Residual
  exact ⟨M22Std.m22_not_standard_of_prop21 hSolZ2A6
      (M22Std.fin77aProp21K_of_harrisSolomonK_of_a6a6 hHarrisSolomon hA6A6) h25
      M22Std.haradaSolomon08M22Split_holds h,
    M23Std.m23_not_standard_of_solomon hSolZ2A7 h,
    M24Std.m24_not_standard_of_gold hHypA hHarrisSolomon M24Std.goldschmidt74Cor4 h⟩

end CFSG.EvenSporadicStandard.Frontier
