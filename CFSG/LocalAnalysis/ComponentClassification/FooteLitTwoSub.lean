module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoSubA7
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoSubL2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsE

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.Foote5

theorem foote5TwoSubgroupOverInner_holds :
    Foote5.Foote5TwoSubgroupOverInner := by
  intro Y _ _ hY R P hP hRP
  rcases hY with he | ⟨p, f, hp, hp2, hf, -, hL⟩
  · obtain ⟨e⟩ := he
    exact TwoSub.twoSub_a7 e R P hP hRP
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
    exact TwoSub.twoSub_l2 e hp hp2 hf hF R P hP hRP

end CFSG.ComponentClassification.FooteLit
