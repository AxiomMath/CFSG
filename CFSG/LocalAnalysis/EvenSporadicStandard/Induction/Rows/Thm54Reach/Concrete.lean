module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.ExcOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.RuCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Inputs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

section Concrete

namespace Thm54Reach

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem ruPerfectCentralizer_holds : RuPerfectCentralizer := by
  intro R _ hR u hu X hX hXu hdvd
  exact card_eq_of_perfect_centralizer_ru hR hu hX hXu hdvd

theorem evenArmInputs_holds : EvenArmInputs where
  sz := fun f => CFSG.LocalAnalysis.EvenBN.GMSK.catSzEvenOuterList f
  sp := CFSG.SeitzReduction.SymplecticPilot.catSp2mEvenOuterExact_holds 2
  su4 := CFSG.SeitzReduction.UnitaryPilot.catSUmEvenOuterAt (by norm_num)
  su5 := CFSG.SeitzReduction.UnitaryPilot.catSUmEvenOuterAt (by norm_num)
  sl4 := CFSG.SeitzReduction.LinearPilot.catSLmEvenOuterAt_of_typeDet (by norm_num)
    (CFSG.SeitzReduction.LinearPilot.slmEvenTypeDetAt (by norm_num))
  sl5 := CFSG.SeitzReduction.LinearPilot.catSLmEvenOuterAt_of_typeDet (by norm_num)
    (CFSG.SeitzReduction.LinearPilot.slmEvenTypeDetAt (by norm_num))
  spCover := by
    intro L _ _ hL hodd n f h
    exact (CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hL hodd h).1

theorem catInputs_holds : CatInputs where
  arm := CFSG.ComponentClassification.CatFC.armInputs_holds
  cardAll := CFSG.ComponentClassification.CatFC.card_carrier_eq_sporOrder_all
  even := evenArmInputs_holds
  ru := ruPerfectCentralizer_holds

theorem excInput_holds : ExcInput :=
  fun h => not_evenStandardException_of_thm54Order h

end Thm54Reach

end Concrete

end CFSG.EvenSporadicStandard.Induction
