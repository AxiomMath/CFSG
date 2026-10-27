module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FinalFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Center
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3HReduce

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.EvenSporadicStandard.TwoFi22 CFSG.LargeExtraspecial.Bridge
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem monsterLocalFourW3Rep : MonsterLocalFourW3Rep :=
  monsterLocalFourW3Rep_of_center_cosetRep_one MW3.center_centralizer_cosetRep_one

theorem twoBGivesM_of_spor_monster (hM : MainStatement) (h210 : DS81Lemma210Two)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25) : TwoBGivesM :=
  twoBGivesM_of_spor_monsterW3 hM h210 hI h25 monsterLocalFourW3Rep

end CFSG.EvenSporadicStandard.TwoB
