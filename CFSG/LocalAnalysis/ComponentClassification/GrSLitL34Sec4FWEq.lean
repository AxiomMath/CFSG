module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single

public section

namespace CFSG.ComponentClassification.GrSLit.FW

open CFSG Subgroup GrS4

variable {X : Type} [Group X] [Finite X]

theorem normalizer_le_of_oddIn_le (hMax : MaximalTwoComponentInput) {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K) (hOK : oddIn K ≤ J) :
    normalizer (W : Set X) ≤ normalizer (K : Set X) := by
  have hKJ : K = J := by
    have h := eq_sup_oddIn_of_singleComponentSetting hs
    rwa [sup_eq_left.mpr hOK] at h
  intro m hm
  rw [hKJ]
  exact (normalizer_eq_of_eq hMax hs hKJ).le hm

theorem not_oddIn_le_of_not_le (hMax : MaximalTwoComponentInput) {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K)
    (hKn : ¬ normalizer (W : Set X) ≤ normalizer (K : Set X)) : ¬ oddIn K ≤ J :=
  fun hOK => hKn (normalizer_le_of_oddIn_le hMax hs hOK)

end CFSG.ComponentClassification.GrSLit.FW
