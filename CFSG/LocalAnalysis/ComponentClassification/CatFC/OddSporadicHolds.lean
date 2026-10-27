module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadic
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.Open.MonsterY443Finiteness

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder sporFactors)
open CFSG.EvenSporadicStandard.Induction


theorem card_carrier_eq_sporOrder_all (s : TauCeti.SporadicName) :
    Nat.card (Carrier s) = sporOrder s := by
  by_cases hM : s = .M
  · subst hM
    rw [AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card]
    norm_num [AGLEmbedding.sporOrd, sporOrder, sporFactors]
  · exact CFSG.ComponentClassification.GSThmB.QPUSpor.card_carrier_eq_sporOrder s hM

theorem oddLieCompNotSporadic_holds : Hyp.OddLieCompNotSporadic :=
  oddLieCompNotSporadic_of_inputs CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput card_carrier_eq_sporOrder_all

end CFSG.ComponentClassification.CatFC
