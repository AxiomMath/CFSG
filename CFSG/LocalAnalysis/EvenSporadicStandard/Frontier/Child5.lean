module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.M10
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.J1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Par
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GoldMain

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child5_of_frontier
    (hCatZ2A6 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)))
    (hCatM10 : CatM10AlmostSimple)
    (hS16Loc : Fin76b.Fin76bOuterS16Loc)
    (hS84 : Fin76b.Fin76bOuterS8₄)
    (hHypA : M24Std.Ega81HypAZ2A8K)
    (hHarrisSolomon : M24Std.HarrisSolomonZ2S6IsoK) :
    J1J3J4Exclusion := by
  intro G _ _ L h
  have hSolZ2A6 := SolomonRed.solomonZ2A6_of_cat hCatZ2A6
  have hSolM10 := SolomonRed.solomonM10_of_cat hCatM10
  exact ⟨J1Std.j1_not_standard h,
    Fin76b.j3_not_standard_of_outerParts hSolZ2A6 hSolM10 hS16Loc Fin76b.extremalParity hS84
      h,
    M24Std.GenX.j4_not_standard_of_gold hHypA hHarrisSolomon M24Std.goldschmidt74Cor4 h⟩

end CFSG.EvenSporadicStandard.Frontier
