
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import CFSG.Sporadic.SmallOddCore.J3DataInputs

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFactsJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFactsJ3
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J2E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathBound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J2
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem fin76bWFacts :
    Fin76bWFacts := by
  intro G _ _ L z t T₀ E Q x β B hconf
  rcases hconf.sporadic with hL | hL
  · exact J2.wFacts_of_isSporadic hconf.cfg hconf.econfig hL
  · exact J3.wFacts_of_isSporadic hconf.cfg hconf.econfig hL

end CFSG.EvenSporadicStandard.Fin76b
