module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2C1c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2C2b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2D1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2D2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2G5b

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd Standing.Setup42

theorem EndB.harris413_L2
    (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hKF : AutPSL2FusionInput) : Harris413L2Case := by
  intro X _ _ _ hnab _ _ t L p f S w z V i j hyp hY
  obtain ⟨hs, h412, -, hsimple, hout⟩ := hyp
  obtain ⟨W, hW, hUW⟩ := hs.exists_W
  have hc : EndB.L2Ctx hs W := ⟨h412, hsimple, hY, hout, hW, hUW⟩
  rcases hs.setup.relIndex_le_four hKF hs.sylow_V hs.le_V with hSV | hSV
  · by_cases hV : IsSylowOf 2 V ⊤
    · exact hc.false_of_isSylowOf_two hKF hKC hV hSV
    · exact hc.false_of_not_isSylowOf_two hKG hKC hFC hKF hV hSV
  · by_cases hV : IsSylowOf 2 V ⊤
    · by_cases hβ : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ V ⊓ centralizer (V : Set X)
      · exact hc.false_of_mem_center hnab hKC hV hβ hSV
      · exact hc.false_of_not_mem_center hKG hKC hFC hV hβ hSV
    · exact hc.false_of_not_isSylowOf_four hKG hKC hFC hV hSV

end CFSG.ComponentClassification.HarrisLit
