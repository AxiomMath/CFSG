module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.StrongP CFSG.Blueprint

section M11


theorem sporadicCaseThreeData_M11 : SporadicCaseThreeData (NativeSporadic.Carrier .M11) := by
  have hc : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 7920 = {2, 3, 5, 11} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end M11

section M12


theorem sporadicCaseThreeData_M12 : SporadicCaseThreeData (NativeSporadic.Carrier .M12) := by
  have hc : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 95040 = {2, 3, 5, 11} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm
      (by rw [hc]; norm_num) hasNoncommPair_three_M12
      (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd)
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end M12

section M22


theorem sporadicCaseThreeData_M22 : SporadicCaseThreeData (NativeSporadic.Carrier .M22) := by
  have hc : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 443520 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end M22

section M23


theorem sporadicCaseThreeData_M23 : SporadicCaseThreeData (NativeSporadic.Carrier .M23) := by
  have hc : Nat.card (NativeSporadic.Carrier .M23) = 10200960 := CFSG.Sporadic.Schreier.m23_card
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 10200960 = {2, 3, 5, 7, 11, 23} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end M23

section M24


theorem sporadicCaseThreeData_M24 : SporadicCaseThreeData (NativeSporadic.Carrier .M24) := by
  have hc : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 244823040 = {2, 3, 5, 7, 11, 23} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm
      (by rw [hc]; norm_num) hasNoncommPair_three_M24
      (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC hodd)
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end M24

section J1


theorem sporadicCaseThreeData_J1 : SporadicCaseThreeData (NativeSporadic.Carrier .J1) := by
  have hc : Nat.card (NativeSporadic.Carrier .J1) = 175560 := CFSG.Sporadic.J1.card_J1
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end J1

end CFSG.AGLEmbedding
