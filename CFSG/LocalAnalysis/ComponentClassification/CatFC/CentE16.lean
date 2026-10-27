module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Inputs
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.Open.MonsterY443Finiteness
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.J1Outer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder sporFactors)



theorem catE16_holds : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.CatE16 :=
  catE16_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
    CatLeafProof.lieOrderFormulasInput
    (fun s => by
      by_cases hM : s = .M
      · subst hM
        rw [AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card]
        norm_num [AGLEmbedding.sporOrd, sporOrder, sporFactors]
      · exact GSThmB.QPUSpor.card_carrier_eq_sporOrder s hM)
    Sporadic.Schreier.at_m11_image_pair_count.2.2.2.2.1
    Sporadic.Schreier.at_j1_schreier.2.1

end CFSG.ComponentClassification.CatFC
