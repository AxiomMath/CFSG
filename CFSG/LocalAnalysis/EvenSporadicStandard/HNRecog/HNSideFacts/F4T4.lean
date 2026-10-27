module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F5T2
public import CFSG.Sporadic.HN.Local.Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open Subgroup CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HN.Local

section Bridge


theorem isConj_hnT4_hnEquivJ_symm_t4J :
    IsConj (hnT4 : NativeSporadic.HN) (hnEquivJ.symm t4J) := by
  have hsq : (hnEquivJ.symm t4J) ^ 2 = 1 := by
    rw [← map_pow, pow_two, t4J_sq, map_one]
  have hne : hnEquivJ.symm t4J ≠ 1 := fun h => t4J_ne_one (by
    have := congrArg hnEquivJ h
    simpa using this)
  rcases hn_involution_cover _ hsq hne with h | h
  · exfalso
    have h1 := card_centralizer_eq_of_isConj' (X := NativeSporadic.HN) h
    have h3 := hn_card_centralizer_t2
    have h2 : Nat.card (centralizer ({hnEquivJ.symm t4J} : Set NativeSporadic.HN)) = 3686400 := by
      rw [@card_centralizer_of_mulEquiv_apply NativeSporadic.HN JH Units.instGroup
        (Subgroup.toGroup _) hnEquivJ _ t4J (hnEquivJ.apply_symm_apply t4J)]
      exact card_CJ_t4
    omega
  · exact h

theorem isExtraspecialPlusByA5WrTwo_centralizer_hnT4 :
    IsExtraspecialPlusByA5WrTwo (centralizer ({hnT4} : Set NativeSporadic.HN)) := by
  have hc : Nonempty (centralizer ({hnEquivJ.symm t4J} : Set NativeSporadic.HN) ≃*
      centralizer ({t4J} : Set JH)) :=
    ⟨@TwoHS.centralizerMulEquiv NativeSporadic.HN JH Units.instGroup (Subgroup.toGroup _)
      hnEquivJ _ _ (hnEquivJ.apply_symm_apply t4J)⟩
  have h4 := @isExtraspecialPlusByA5WrTwo_of_nonempty_mulEquiv JH NativeSporadic.HN
    (Subgroup.toGroup _) Units.instGroup t4J (hnEquivJ.symm t4J) hc
    isExtraspecialPlusByA5WrTwo_CJ
  exact isExtraspecialPlusByA5WrTwo_of_isConj (X := NativeSporadic.HN)
    isConj_hnT4_hnEquivJ_symm_t4J h4

end Bridge

end CFSG.EvenSporadicStandard.HNRecog.SideF4
