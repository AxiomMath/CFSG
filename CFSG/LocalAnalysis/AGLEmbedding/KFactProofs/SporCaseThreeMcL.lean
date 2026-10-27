module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeMcLThree

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_McL : SporadicCaseThreeData (NativeSporadic.Carrier .McL) := by
  have hc : Nat.card (NativeSporadic.Carrier .McL) = 898128000 := CFSG.Sporadic.McL.card_McL
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 898128000 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_McL_three
  · intro _ _
    exact sporCaseThreePrimeData_McL_five
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
