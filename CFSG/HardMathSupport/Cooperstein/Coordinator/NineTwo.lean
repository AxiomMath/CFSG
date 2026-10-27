module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

theorem asc81bNineTwo_of (h : FFModuleTheorem) : Asc81bNineTwo := by
  intro G _ _ X S L hX hA hL
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  let _ := blockVCommGroup S L
  have hV2 : ∀ v : ↥(blockV S L), v ^ 2 = 1 := fun v =>
    Subtype.ext ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf
      (pCoreOf 2 (L ⊔ S))).2 (v : G) v.2)
  have hFF := isFFModule_autOn_blockV hA hL hSL
  have hhyp := ffHyp_autOn hA hL hSL hX
  obtain ⟨e⟩ := nonempty_autOnCenterQuotientEquiv hA hL hSL
  rcases h _ hV2 _ _ hhyp hFF with (⟨d, hd, ⟨g⟩⟩ | ⟨n, hn, ⟨g⟩⟩ | ⟨d, hd, ⟨g⟩⟩) | ⟨m, hm, ⟨f⟩⟩
  · exact Or.inl (Or.inl ⟨d, hd, ⟨e.symm.trans g⟩⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans g⟩⟩))
  · exact Or.inl (Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans g⟩⟩))
  · exact Or.inr ⟨m, hm, ⟨e.symm.trans f⟩⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator
