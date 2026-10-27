
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

theorem wFacts_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) (hL : IsSporadic L .J3) :
    WFacts L t E := by
  obtain ⟨e⟩ := hL
  obtain ⟨T, Ex, tx, hM⟩ := pinModel_j3P
  exact wFacts_of_model h hE (j3PermEquiv.symm.trans e.symm) hM rootFactsClass_j3P

end CFSG.EvenSporadicStandard.Fin76b.J3
