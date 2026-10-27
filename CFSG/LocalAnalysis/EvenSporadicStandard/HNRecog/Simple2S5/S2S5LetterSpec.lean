module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Letters

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

theorem elemW_nil_eq_one : elemW [] = 1 := by
  simp [elemW, TwoHS.wordVal]

theorem elemW_expandL_mem {S : Subgroup (Equiv.Perm (Fin 1408))} {subs : List (List Nat)}
    (h : ∀ w ∈ subs, elemW w ∈ S) (l : List Nat) : elemW (expandL subs l) ∈ S := by
  induction l with
  | nil => rw [expandL, List.flatMap_nil, elemW_nil_eq_one]; exact S.one_mem
  | cons i l ih =>
    rw [expandL, List.flatMap_cons, elemW_append]
    refine S.mul_mem ?_ ih
    by_cases hi : i - 1 < subs.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega), elemW_nil_eq_one]
      exact S.one_mem

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
