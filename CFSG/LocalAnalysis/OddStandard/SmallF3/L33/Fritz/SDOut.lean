module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDCtxBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDConfigOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDCaseKD

public section

namespace CFSG.OddStandard.SmallF3.L33.KD

open Subgroup CFSG.ComponentClassification.HSFLit

theorem exists_sdCtx
    (hH : HaradaInput) {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}
    (h : FritzHyp X t L) : Nonempty (SDCtx X t L) := by
  obtain ⟨M⟩ := SDModel.exists_sdModel h.model
  obtain ⟨A, hA⟩ := SDPsi.exists_sdData (sdConfig_of_hyp h M) M
  obtain ⟨C⟩ := SDCaseKD.exists_caseKD hH h.not_sectRank4 A
  obtain ⟨S⟩ := SD.nonempty_gens (A := A)
  exact ⟨⟨M, A, hA, C, S, h.isPGroup_K⟩⟩

end CFSG.OddStandard.SmallF3.L33.KD
