module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo1Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo1Five
public import CFSG.Sporadic.Co1

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Co1 : SporadicCaseThreeData (NativeSporadic.Carrier .Co1) := by
  have hc : Nat.card (NativeSporadic.Carrier .Co1) = 4157776806543360000 :=
    CFSG.Sporadic.Co1.card_Co1
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 4157776806543360000 = {2, 3, 5, 7, 11, 13, 23} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_Co1_three
  · intro _ _
    exact sporCaseThreePrimeData_Co1_five
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
