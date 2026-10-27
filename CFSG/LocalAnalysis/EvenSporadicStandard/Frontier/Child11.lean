module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HResidual
public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main
public import CFSG.LargeExtraspecial.S14Main

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child11_of_frontier
    (hGH74 : CFSG.LargeExtraspecial.AS35W.GH74Models)
    (hDS210 : TwoB.DS81Lemma210Two) :
    TwoBGivesM :=
  TwoB.twoBGivesM_of_spor_monster (CFSG.LargeExtraspecial.S14.mainStatement_of_inputs ⟨hGH74⟩)
      hDS210 (HypOne.BabyHyp.hypothesisOne_B HypOne.BabyHyp.babyNoOrder68)
      (Finkelstein77.Lemma25HProof.asc76Lemma25_of_hallQ8Residual
          ComponentClassification.Foote5.HallGen.hallQ8Residual)

end CFSG.EvenSporadicStandard.Frontier
