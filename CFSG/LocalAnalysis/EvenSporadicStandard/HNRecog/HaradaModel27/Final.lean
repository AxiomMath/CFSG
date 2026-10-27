module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Facts2P
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.FactsAllP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.LiftTrue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Unique
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Facts

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

section Cert


theorem haradaInterfaceAll_holds : Harada.S25.HaradaInterfaceAll :=
  haradaInterfaceAll_of_P exists_mulEquiv_p1408_of_isF5Centralizer
    (fun h => card_P1408 (hsCtx_of_isHSCover h.toIsHSCover))
    (fun hP hF hE => ⟨_, _, _, _, _, _, _, _, _, _, _, _,
      haradaFactsAll_P (haradaFacts2_P (twoHSFacts_P1408 hP hF hE) hE hF.normal)
        (cent3Facts_P hP) hP liftOK_true⟩)

theorem setting25Exists_holds (hGH : GH73.GH73TheoremA64K) : Harada.Setting25Exists :=
  Harada.S25.setting25Exists_of_interfaceAll haradaInterfaceAll_holds hGH

end Cert

end CFSG.EvenSporadicStandard.HNRecog
