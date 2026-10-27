module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1517bRes
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bRed
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bKB

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem o1517bGen_of_inputs
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (hKB : KFactE9AutTwoThree) : O1517bGen := by
  intro G _ _ hC M hM _ hstrong p hp R hR hΓ A hAM hA hpA P hP hPs
  rcases o1517b_le_or_red hC hM hstrong hp hR hΓ hAM hA hpA hP hPs with hle | hred
  · exact hle
  · exact (O1517bRed.false hKA hKB hred).elim

theorem o1517bGen_of_gls3
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (hGLS : Gls3StronglyThreeEmbeddedPlus) :
    O1517bGen :=
  o1517bGen_of_inputs hKA (kFactE9AutTwoThree_of_gls3 hGLS)

theorem o1517b_of_gls3
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (hGLS : Gls3StronglyThreeEmbeddedPlus) :
    CFSG.LocalAnalysis.RankThreeUC.S15.O1517b :=
  o1517b_of_gen (o1517bGen_of_gls3 hKA hGLS)

theorem o1517bRes_of_gls3
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (hGLS : Gls3StronglyThreeEmbeddedPlus) :
    CFSG.LocalAnalysis.RankThreeUC.S15.O1517bRes := by
  intro G _ _ hS hUC M hM hwit hstrong p hp _ R hR hΓ A hAM hA hpA P hP hPs _
  exact o1517b_of_gls3 hKA hGLS G hS hUC M hM hwit hstrong p hp R hR hΓ A hAM hA hpA P hP hPs

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
