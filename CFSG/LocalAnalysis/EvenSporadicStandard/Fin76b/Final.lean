
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65
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

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65Facts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem fin76bLemma65b_of_residuals
    (h1 : Fin76bNoOrderEight) (h2 : Fin76bNoKleinFour) : Fin76bLemma65b :=
  fin76bLemma65b_of_bound fin76bWFacts (fin76bBound_of_residuals h1 h2)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end CFSG.EvenSporadicStandard.Fin76b
