module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsF
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL24VL2

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.Foote5

theorem foote5Lemma24iiV_holds :
    Foote5.Foote5Lemma24iiV := by
  intro 𝕊 _ _ h𝕊 V hV hVI P hP
  rcases h𝕊 with he | ⟨p, n, hp, hp2, hn, -, hL⟩
  · obtain ⟨e⟩ := he
    obtain ⟨f, -, hf⟩ := L24V.l24V_a7 e hV hVI hP
    exact ⟨f, hf⟩
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
    obtain ⟨f, -, hf⟩ := L24V.l24V_l2 (AutL2Facts.isOddPrimePower_of hp hp2 hn hF) e hV hVI hP
    exact ⟨f, hf⟩

end CFSG.ComponentClassification.FooteLit
