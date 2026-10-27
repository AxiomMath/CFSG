module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeFi24Seven
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeFi24Three

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Fi24Prime_of_three
    (h3 : ∀ [Finite (NativeSporadic.Carrier .Fi24Prime)] [Fact (Nat.Prime 3)],
      SporCaseThreePrimeData (NativeSporadic.Carrier .Fi24Prime) 3) :
    SporadicCaseThreeData (NativeSporadic.Carrier .Fi24Prime) := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi24Prime) = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 1255205709190661721292800 = {2, 3, 5, 7, 11, 13, 17, 23, 29} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact h3
  · intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)
  · intro _ _
    exact sporCaseThreePrimeData_Fi24_seven
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

section Full


theorem sporadicCaseThreeData_Fi24Prime :
    SporadicCaseThreeData (NativeSporadic.Carrier .Fi24Prime) :=
  sporadicCaseThreeData_Fi24Prime_of_three sporCaseThreePrimeData_Fi24_three

end Full

end CFSG.AGLEmbedding
