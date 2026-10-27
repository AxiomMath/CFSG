module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS7
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS5

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

theorem harris415ComponentStep_of
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (h34 : Harris81Lemma34Input) (h46c : Harris46cInput) (h46d : Harris46dInput)
    (h39 : Harris82TheoremOneKProper) (h36 : Harris81Lemma36NonsimpleInput)
    (hin : Harris36SimpleInput) (hJ2 : TwoJ2OuterInvolutionIndexFact)
    (hHS : TwoHSInnerInvolutionIndexFact)
    (hL34 : GrSLit.L34OuterInvolutionCentralizerFact)
    (hSm : Harris415SmallTypesIndexFact) (hL3 : EndB.L3U3InvolutionSL2Fact) :
    Harris415ComponentStep := by
  intro X _ _ _ hnab hK hcat t L p f S w z V i j ⟨hs, h412, h47, hnq⟩ z₁ τ α K₂ W 𝒱 fd
  have hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱 := ⟨hs, h412, h47, hnq, fd⟩
  obtain ⟨M, hM, -, hKM, hKpc, hinv, hsyl, hcard⟩ := hD.exists_component hnab hK hSch
  have hlt := hD.K₂F_lt hKM hinv
  have hnβ := hD.not_conj_beta hM hlt
  obtain ⟨hMeq, hF, hZ⟩ := hD.layer_eq_of_lemma46 hnab hK hcat h46c h46d hnβ hM hlt
  subst hMeq
  have hEs := hD.isSimpleGroup_layer hnab hK hcat h39 h36 hJ2 hHS hL34 hnβ hM rfl hF hZ hlt
    hKpc hsyl hcard
  rcases hD.list_of_alpha hnab hK hSch hFC hKC h34 hin hnβ hM hEs hF hlt with
    h | h | h | h | h | h
  · exact hD.not_small_types hSm hM rfl hlt hKpc hsyl hcard hnβ (Or.inl h)
  · exact hD.not_small_types hSm hM rfl hlt hKpc hsyl hcard hnβ (Or.inr (Or.inl h))
  · exact hD.not_small_types hSm hM rfl hlt hKpc hsyl hcard hnβ (Or.inr (Or.inr h))
  · exact hD.not_L3U3 hnab hK hSch hL3 hM hEs hlt (Or.inl h)
  · exact hD.not_L3U3 hnab hK hSch hL3 hM hEs hlt (Or.inr h)
  · exact hD.not_L2 hnβ hlt hsyl (hasDihedralSylowTwo_of_lieModel_psl2 hD.hs.p_ne_two h)

end CFSG.ComponentClassification.HarrisLit
