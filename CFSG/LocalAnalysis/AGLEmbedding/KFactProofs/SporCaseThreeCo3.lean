module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo3Three

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Co3 : SporadicCaseThreeData (NativeSporadic.Carrier .Co3) := by
  have hc : Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 := CFSG.Sporadic.Co3.card_Co3
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 495766656000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_Co3_three
  · intro _ _
    exact sporCaseThreePrimeData_Co3_five
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
