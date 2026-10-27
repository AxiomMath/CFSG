module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Close
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13BalancedProps

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

theorem lemma32InputFor_simple_of_twoPart (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) : Lemma32InputFor simpleAmbient :=
  lemma32InputFor_of_twoPart hq (fun _ _ _ hG => kStarKProper_of_simpleAmbient hG) hR1
    fun _ _ _ hG _ hN' => not_le_solomonKStarOf_top_of_simple hG hN'

theorem lemma32ConditionTwoInputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma32ConditionTwoInputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

theorem solomonThm13Simple_of_twoPart
        (h33 : Lemma33InputFor simpleAmbient) (hres : Lemma313ResidueInputFor simpleAmbient)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h315a : Lemma315aInputFor simpleAmbient)
    (h315c : Lemma315cInputFor simpleAmbient) (hq : QuasisimpleTwoPartInput) :
    SolomonThm13Simple :=
  solomonThm13Simple_of_noncentral h33 hres (lemma32InputFor_simple_of_twoPart hq hR1) h315a
    h315c hq

end CFSG.ComponentClassification.Sol76T13
