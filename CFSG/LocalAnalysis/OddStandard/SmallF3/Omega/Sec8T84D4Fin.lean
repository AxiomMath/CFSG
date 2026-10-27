module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D2Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D4Asm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma811KCore_of (F : Sec8T84Base) (_h89 : Asc82Lemma89) (h810 : Asc82Lemma810K) :
    Asc82Lemma811KCore := by
  intro G _ _ hK t L S z g B E hE
  obtain ⟨X1, X2, hX⟩ := h810 G hK t L S z g B E hE
  have hctx : Sec8T84DCtx G t E X1 X2 := sec8t84d2_ctx F.hCE hE hX
  obtain ⟨E1, E2, hd⟩ := sec8t84d2_dec hctx
  exact ⟨Sec8T84Y X1, Sec8T84Y X2, sec8t84d4_core hctx hd⟩

theorem asc82Lemma811K_of_split (F : Sec8T84Base) (h89 : Asc82Lemma89) (h810 : Asc82Lemma810K)
    (hS : Sec8T84SplitK) : Asc82Lemma811K :=
  asc82Lemma811K_of_core_split (asc82Lemma811KCore_of F h89 h810) hS

end CFSG.OddStandard.SmallF3.Omega
