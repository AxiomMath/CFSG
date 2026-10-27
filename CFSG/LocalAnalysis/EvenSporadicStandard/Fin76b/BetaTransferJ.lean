
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

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFactsJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFactsJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5J3
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J2E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J2
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j2P j2PermEquiv j3P j3PermEquiv)

namespace J2

theorem betaData65_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hW : WFacts L t E) (hE2 : IsPGroup 2 E)
    (hL : IsSporadic L .J2) {β : G} (hβL : β ∈ L) (hβt : β * t = t * β) (hβ3 : orderOf β = 3) :
    BetaData65 E β := by
  obtain ⟨e⟩ := hL
  have hB : BetaDataSqB ↥ComponentClassification.J2Cover.Models.P :=
    BetaDataSqB.of_mulEquiv
      ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
        (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
      betaDataSqB_j2P
  exact betaData65_of_wFacts hW hE2 hβL hβt hβ3
    (a6_quotient_of_model h
      (((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
        ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm) hB.betaDataSq
      rootFactsClass_P hβL hβt hβ3)

end J2

namespace J3

theorem betaData65_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hW : WFacts L t E) (hE2 : IsPGroup 2 E)
    (hL : IsSporadic L .J3) {β : G} (hβL : β ∈ L) (hβt : β * t = t * β) (hβ3 : orderOf β = 3) :
    BetaData65 E β := by
  obtain ⟨e⟩ := hL
  exact betaData65_of_wFacts hW hE2 hβL hβt hβ3
    (a6_quotient_of_model h (j3PermEquiv.symm.trans e.symm) betaDataSqB_j3P.betaDataSq
      rootFactsClass_j3P hβL hβt hβ3)

end J3

theorem fin76bBetaData :
    Fin76bBetaData := by
  intro G _ _ L z t T₀ E Q x β B hconf hW
  have hE2 : IsPGroup 2 E := hconf.cfg.T₀_pgroup.to_le hconf.econfig.le
  have hβL : β ∈ L := hconf.B_le hconf.beta_mem
  have hβt : β * t = t * β := mem_centralizer_singleton_iff.1 (hconf.B_cent hconf.beta_mem)
  rcases hconf.sporadic with hL | hL
  · exact J2.betaData65_of_isSporadic hconf.cfg hW hE2 hL hβL hβt hconf.beta_order
  · exact J3.betaData65_of_isSporadic hconf.cfg hW hE2 hL hβL hβt hconf.beta_order

theorem fin76bNoOrderEight :
    Fin76bNoOrderEight :=
  fin76bNoOrderEight_of_betaData fin76bBetaData

end CFSG.EvenSporadicStandard.Fin76b
