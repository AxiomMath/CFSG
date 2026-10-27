module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCCA7Swap
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCCA7Triple
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCCL2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5InputsD

public section

namespace CFSG.ComponentClassification.FooteLit.FCC

open CFSG Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7)

theorem fcc_a7 (β : MulAut A7) (hβ2 : β * β = 1) (hβ : β ∉ innAut5 A7) :
    ∃ M, FCConcl A7 β M :=
  fcc_a7_of_models fcc_swap45 fcc_triple β hβ2 hβ

theorem fcc_of_a7 {Y : Type} [Group Y] (e : Y ≃* A7) (β : MulAut Y) (hβ2 : β * β = 1)
    (hβ : β ∉ innAut5 Y) : ∃ M, FCConcl Y β M := by
  obtain ⟨M, hM⟩ := fcc_a7 (MulAut.congr e β) (by rw [← map_mul, hβ2, map_one])
    (by rwa [Aut5.congr_mem_innAut5_iff])
  have h := hM.map e.symm
  have hβ' : MulAut.congr e.symm (MulAut.congr e β) = β := by
    ext y
    simp [MulAut.congr_apply]
  rw [hβ'] at h
  exact ⟨_, h⟩

end CFSG.ComponentClassification.FooteLit.FCC

namespace CFSG.ComponentClassification.FooteLit

theorem foote5FieldCentralizerC_holds :
    Foote5.Foote5FieldCentralizerC := by
  intro Y _ _ hY β hβ2 hβ hR
  rcases hY with he | ⟨p, f, hp, hp2, hf, -, hL⟩
  · obtain ⟨e⟩ := he
    obtain ⟨M, hM⟩ := FCC.fcc_of_a7 e β hβ2 hβ
    exact FCC.foote5FCC_of hM
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
    obtain ⟨M, hM⟩ := FCC.fcc_l2 e hp hp2 hf hF β hβ2 hβ hR
    exact FCC.foote5FCC_of hM

end CFSG.ComponentClassification.FooteLit
