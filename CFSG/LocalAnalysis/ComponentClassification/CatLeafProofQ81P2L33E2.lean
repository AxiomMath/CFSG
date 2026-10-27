module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Untw
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2D4

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem twoNilpFor_of_E6
    (hG2 : InvolutionCentralizerNotTwoGroup .G2) (hF4 : InvolutionCentralizerNotTwoGroup .F4)
    (hE7 : InvolutionCentralizerNotTwoGroup .E7) (hE8 : InvolutionCentralizerNotTwoGroup .E8)
    (hD4 : InvolutionCentralizerNotTwoGroup .trialityD4)
    (hE6 : TwoNilpFor (fun Y _ => ∃ t f, (t = .E6 ∨ t = .twistedE6) ∧
      ChevalleyExceptionalModel Y t 2 f)) :
    TwoNilpFor (fun Y _ => ∃ t f, t ∈ chevalleyExceptionalTags ∧
      ChevalleyExceptionalModel Y t 2 f) := by
  intro Y _ _ hY hs hnab a ha hP
  obtain ⟨t, f, ht, hm⟩ := hY
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hP (untwisted_model_not_isPGroup (Or.inl rfl) hG2 hm hs a ha)
  · exact absurd hP (untwisted_model_not_isPGroup (Or.inr (Or.inl rfl)) hF4 hm hs a ha)
  · exact hE6 Y ⟨_, f, Or.inl rfl, hm⟩ hs hnab a ha hP
  · exact absurd hP (untwisted_model_not_isPGroup (Or.inr (Or.inr (Or.inl rfl))) hE7 hm hs a ha)
  · exact absurd hP (untwisted_model_not_isPGroup (Or.inr (Or.inr (Or.inr rfl))) hE8 hm hs a ha)
  · exact hE6 Y ⟨_, f, Or.inr rfl, hm⟩ hs hnab a ha hP
  · exact absurd hP (triality_model_not_isPGroup hD4 hm hs a ha)

end CFSG.ComponentClassification.HarrisLit.L33.E2
