module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.KFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction.Hyp


theorem ONOuterFixedPerfect.of_fixedJ1 (h : ONOuterFixedJ1) : ONOuterFixedPerfect := by
  intro Y _ hY ν hν hout
  obtain ⟨e⟩ := h Y hY ν hν hout
  have hcard : Nat.card ↥(fixSubgroup ν) = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have hs : IsSimpleGroup ↥(fixSubgroup ν) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J1.isSimpleGroup_J1 e
  have : Finite ↥(fixSubgroup ν) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnc : ∃ a b : ↥(fixSubgroup ν), a * b ≠ b * a :=
    nonabelian_of_isSimpleGroup_of_not_prime (by rw [hcard]; norm_num)
  exact ⟨fixSubgroup ν, le_rfl, (isQuasisimple_of_simple_nonabelian hs hnc).1, by
    rw [hcard]; norm_num⟩

end CFSG.EvenSporadicStandard.Induction
