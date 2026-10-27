module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeFi23Three
public import CFSG.Sporadic.Fi23.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Fi23 : SporadicCaseThreeData (NativeSporadic.Carrier .Fi23) := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 4089470473293004800 = {2, 3, 5, 7, 11, 13, 17, 23} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_Fi23_three
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
