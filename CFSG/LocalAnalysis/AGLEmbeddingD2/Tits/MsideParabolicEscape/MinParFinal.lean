module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParFamily
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParResTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParResRee

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.AGLEmbeddingD2.GN

set_option linter.unusedSectionVars false


theorem minParResidualCase_proved : MinParResidualCase := by
  intro Y _ _ L R P hL hres hR hR2 hS hP
  rcases hres with he | ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    exact kFact_of_alt_six hR hR2 hS hP e
  · exact kFact_of_u33 hR hR2 hS hP d q hq hdq e
  · obtain ⟨dd, hv⟩ := d
    rcases hd with ⟨m, hm⟩ | ⟨m, hm⟩ | hm
    · simp only at hm
      subst hm
      exact kFact_of_suzuki hL hR hR2 hS hP m hv e
    · simp only at hm
      subst hm
      exact kFact_of_reeF4 hR hR2 hS hP m hv e
    · simp only at hm
      subst hm
      exact kFact_of_tits hR hR2 hS hP hv e

theorem kFactChevMinParabolic_proved : GN.KFactChevMinParabolic :=
  kFactChevMinParabolic_of_residual minParResidualCase_proved

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
