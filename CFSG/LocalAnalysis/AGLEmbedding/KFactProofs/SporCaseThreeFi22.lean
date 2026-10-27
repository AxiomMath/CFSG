module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeFi22Three
public import CFSG.Sporadic.Fi22.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint


theorem sporadicCaseThreeData_Fi22 : SporadicCaseThreeData (NativeSporadic.Carrier .Fi22) := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 64561751654400 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_Fi22_three
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end CFSG.AGLEmbedding
