module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeONThree

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_ON : SporadicCaseThreeData (NativeSporadic.Carrier .ONan) := by
  have hc : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 460815505920 = {2, 3, 5, 7, 11, 19, 31} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_ON_three
  · intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)
  · intro _ _
    exact sporCaseThreePrimeData_ON_seven
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
