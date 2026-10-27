module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSmallPSL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSmallA6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSmallU33
public import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127
  CFSG.QuasithinUnique.Bridge.Over

set_option linter.unusedSectionVars false


theorem kFactChevGenThree_proved : KFactChevGenThree := by
  intro Y _ _ L S₀ hL hcl hS
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hdq, ⟨e⟩⟩
  · exact chevGen_lieIndex hL hS d hd e
  · rcases hn with rfl | rfl | rfl
    · exact chevGen_of_hasBorelModel hL hS (hasBorelModel_alt_five e)
    · exact chevGen_of_yData hL hS
        (YData.of_mulEquiv_sylow e Even6.isSylow_D yData_alt_six
          (isSylowTwoOf_top_map_center hS))
    · exact chevGen_of_hasBorelModel hL hS (hasBorelModel_alt_eight e)
  · rcases hdq with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      exact chevGen_of_hasBorelModel hL hS (hasBorelModel_model_seven h)
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at h
      obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
      exact chevGen_of_yData hL hS
        (YData.of_mulEquiv_sylow e' CertU33.isSylow_D yData_u33
          (isSylowTwoOf_top_map_center hS))

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
