module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeHNThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeHNFive
public import CFSG.Sporadic.HN

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_HN : SporadicCaseThreeData (NativeSporadic.Carrier .HN) := by
  have hc : Nat.card (NativeSporadic.Carrier .HN) = 273030912000000 :=
    CFSG.Sporadic.HN.card_HN
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 273030912000000 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_HN_three
  · intro _ _
    exact sporCaseThreePrimeData_HN_five
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
