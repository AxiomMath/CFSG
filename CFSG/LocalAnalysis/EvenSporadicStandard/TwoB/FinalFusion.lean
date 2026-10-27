module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FinalNoSection
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma54Final
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionMonsterW3

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.EvenSporadicStandard.TwoFi22 CFSG.LargeExtraspecial.Bridge
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem twoBGivesM_of_spor_w3 (hM : MainStatement) (h210 : DS81Lemma210Two)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25)
    (h3 : TwoBLocalFourW3) : TwoBGivesM :=
  twoBGivesM_of_hypothesisOne_direct hM
      (ds81Lemma54_of_schreier CFSG.RankThree.PartOne.SPOR.schreierFor_catalog hI h25 h210) hI h25
      (ds81Lemma55Fusion_of_w3 babyTableIII h3)

theorem twoBGivesM_of_spor_w3Rep (hM : MainStatement) (h210 : DS81Lemma210Two)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25)
    (h3 : TwoBLocalFourW3Rep) : TwoBGivesM :=
  twoBGivesM_of_spor_w3 hM h210 hI h25 (twoBLocalFourW3_of_rep babyTableIII h3)

theorem twoBGivesM_of_spor_monsterW3 (hM : MainStatement) (h210 : DS81Lemma210Two)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25)
    (h : MonsterLocalFourW3Rep) : TwoBGivesM :=
  twoBGivesM_of_spor_w3Rep hM h210 hI h25 (twoBLocalFourW3Rep_of_monster h)

end CFSG.EvenSporadicStandard.TwoB
