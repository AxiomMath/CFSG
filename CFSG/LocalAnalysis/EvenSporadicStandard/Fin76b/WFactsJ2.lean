
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j2P j2PermEquiv)

theorem rootFactsClass_P :
    RootFactsClass ↥ComponentClassification.J2Cover.Models.P :=
  RootFactsClass.of_mulEquiv
    ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
      (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
    rootFactsClass_j2P

theorem wFacts_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) (hL : IsSporadic L .J2) :
    WFacts L t E := by
  obtain ⟨e⟩ := hL
  obtain ⟨T, Ex, tx, hM⟩ := pinModel_P
  exact wFacts_of_model h hE
    (((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
      ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm) hM rootFactsClass_P

end CFSG.EvenSporadicStandard.Fin76b.J2
