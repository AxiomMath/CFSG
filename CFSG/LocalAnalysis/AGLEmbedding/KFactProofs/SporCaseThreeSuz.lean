module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeSuzThree
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Suz : SporadicCaseThreeData (NativeSporadic.Carrier .Suz) := by
  have hc : Nat.card (NativeSporadic.Carrier .Suz) = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 448345497600 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_Suz_three
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
