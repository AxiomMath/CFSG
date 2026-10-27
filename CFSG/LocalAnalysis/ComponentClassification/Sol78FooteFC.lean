module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCA7
public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCL2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsB

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.ComponentClassification.Foote5


theorem foote5FieldCentralizer : Foote5FieldCentralizer := by
  intro Y _ _ hY
  rcases id hY with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, -, -, hL⟩
  · exact ⟨fun β hβ2 hβ _ => fieldCentralizer_a_alt7 e hβ2 hβ,
      fun W hW γ _ hγ E hE => fieldCentralizer_b_alt7 e hW hγ hE⟩
  · refine ⟨fun β hβ2 hβ hR => fieldCentralizer_a_psl2 hp hp2 hL hβ2 hβ hR,
      fun W hW γ _ hγ E hE => ?_⟩
    obtain ⟨-, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
    exact not_isKleinFour_of_centralizer hY (conj_injective_of_footeSimpleType hY)
      (fun _ _ haW => mem_of_centralizes_kleinFour_psl2
        (AutL2Facts.isOddPrimePower_of hp hp2 hf hF) e hW haW) hγ hE

end CFSG.ComponentClassification.Sol78
