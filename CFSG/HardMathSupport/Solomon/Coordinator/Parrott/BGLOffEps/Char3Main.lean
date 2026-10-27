module

public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3Join
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLHolds

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremB

section Certified


theorem bglOffEpsCharThree_holds : BGLOffEpsCharThree := by
  intro K _ _ hK hT f x hf hf1 hf3 hx hx1 hx3 hfx
  refine le_sup_of_le_right ?_
  rcases hT with ⟨F, hF, hFfin, -, he⟩ | ⟨F, hF, hFfin, q, hcard, hq3, he⟩
  · exact bglFieldGenerationThreeL_holds K hK ⟨F, hF, hFfin, he⟩ f x hf hf1 hf3 hx hx1 hx3 hfx
  · have h := Char3.bglu_pair_generation_any hK ⟨F, hF, hFfin, q, hcard, by omega, he⟩
      hf hf1 hf3 hx hx1 hx3 hfx
    refine h.trans (sup_le ?_ ?_)
    · refine le_trans (sSup_le fun L hL => hL.1) ?_
      refine le_iSup₂_of_le 0 (by norm_num) ?_
      simp
    · refine le_trans (sSup_le fun L hL => hL.1) ?_
      refine le_iSup₂_of_le 1 (by norm_num) ?_
      simp

end Certified

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps
