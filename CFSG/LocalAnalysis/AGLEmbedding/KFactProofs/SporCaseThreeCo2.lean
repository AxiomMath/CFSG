module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo2Three

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Co2 : SporadicCaseThreeData (NativeSporadic.Carrier .Co2) := by
  have hc : Nat.card (NativeSporadic.Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 42305421312000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_Co2_three
  · intro _ _
    exact sporCaseThreePrimeData_Co2_five
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
