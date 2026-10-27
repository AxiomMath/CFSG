module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.M10
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Par

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child12_of_frontier
    (hCatZ2A6 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)))
    (hCatM10 : CatM10AlmostSimple)
    (hS16Loc : Fin76b.Fin76bOuterS16Loc)
    (hS84 : Fin76b.Fin76bOuterS8₄) :
    J2Exclusion := by
  intro G _ _ L h
  have hSolZ2A6 := SolomonRed.solomonZ2A6_of_cat hCatZ2A6
  have hSolM10 := SolomonRed.solomonM10_of_cat hCatM10
  exact Fin76b.j2_not_standard_of_outerParts hSolZ2A6 hSolM10 hS16Loc Fin76b.extremalParity hS84
    h

end CFSG.EvenSporadicStandard.Frontier
