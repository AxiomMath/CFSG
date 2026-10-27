module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall3
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.StrongP CFSG.Blueprint

section J2


theorem sporadicCaseThreeData_J2 : SporadicCaseThreeData (NativeSporadic.Carrier .J2) := by
  have hc : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 604800 = {2, 3, 5, 7} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_J2
      (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hC hodd)
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end J2

section J4


theorem sporadicCaseThreeData_J4 : SporadicCaseThreeData (NativeSporadic.Carrier .J4) := by
  have hc : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  have hord : CFSG.SectionRank.J4OrderHyp := dvd_of_eq CFSG.Sporadic.J4.card_J4
  have hkt : ∀ {p : ℕ} [Fact p.Prime], p ≠ 2 → KernelTrivialAt (NativeSporadic.Carrier .J4) p :=
    fun hp2 => kernelTrivialAt_of_odd hp2 fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.J4_perfect_odd_cover_trivial hord π hπ hC hodd
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 86775571046077562880 = {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_J4
      (hkt (by norm_num))
  · intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)
  · intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num)
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_J4 (hkt (by norm_num))
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end J4

section HS


theorem sporadicCaseThreeData_HS : SporadicCaseThreeData (NativeSporadic.Carrier .HS) := by
  have hc : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 44352000 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num)
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_HS
      (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.HS_perfect_odd_cover_trivial π hπ hC hodd)
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end HS

section He


theorem sporadicCaseThreeData_He : SporadicCaseThreeData (NativeSporadic.Carrier .He) := by
  have hc : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
  have hkt : ∀ {p : ℕ} [Fact p.Prime], p ≠ 2 → KernelTrivialAt (NativeSporadic.Carrier .He) p :=
    fun hp2 => kernelTrivialAt_of_odd hp2 fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.He_perfect_odd_cover_trivial π hπ hC hodd
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 4030387200 = {2, 3, 5, 7, 17} := by norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_He
      (hkt (by norm_num))
  · intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num)
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_He (hkt (by norm_num))
  · intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end He

section Ru


theorem sporadicCaseThreeData_Ru : SporadicCaseThreeData (NativeSporadic.Carrier .Ru) := by
  have hc : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  have hkt : ∀ {p : ℕ} [Fact p.Prime], p ≠ 2 → KernelTrivialAt (NativeSporadic.Carrier .Ru) p :=
    fun hp2 => kernelTrivialAt_of_odd hp2 fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.Ru_perfect_odd_cover_trivial π hπ hC hodd
  refine sporadicCaseThreeData_of_card hc (by norm_num) ?_
  have hpf : Nat.primeFactors 145926144000 = {2, 3, 5, 7, 13, 29} := by
    norm_num [Nat.primeFactors]
  intro p hp hp2
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_Ru
      (hkt (by norm_num))
  · intro _ _
    exact sporCaseThreePrimeData_of_noncomm (by rw [hc]; norm_num)
      CFSG.RankThree.PartOne.CTP.hasNoncommPair_Ru (hkt (by norm_num))
  all_goals
    intro _ _
    exact sporCaseThreePrimeData_of_not_dvd (by rw [hc]; norm_num)

end Ru

end CFSG.AGLEmbedding
