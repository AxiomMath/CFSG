module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeThThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubic

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Th : SporadicCaseThreeData (NativeSporadic.Carrier .Th) := by
  have hc : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.PartOne.CTP.card_Th
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_Th_three
  · intro _ _
    exact sporCaseThreePrimeData_Th_five
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
