module

public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.Assembly.OpenBridges
import CFSG.Foundations.KCoreClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census

section Transfer

variable {G H : Type} [Group G] [Finite G] [Group H]

theorem Standing.false_of_not_isCharTwoType (hS : Standing G) (e : G ≃* H)
    (hH : ¬ IsCharTwoType H) : False :=
  hH (isCharTwoType_of_mulEquiv e hS.charTwo)

theorem Standing.false_of_localRank_le_two (hS : Standing G) (e : G ≃* H)
    (h : ∀ [Finite H] (r : ℕ), r.Prime → r ≠ 2 → localRank r H ≤ 2) : False := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  have h3 : evenRank G = 3 := (evenRank_eq_open G).trans hS.rank
  have hle : evenRank G ≤ evenRank H :=
    CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e
  have h2 : evenRank H ≤ 2 := CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le h
  omega

theorem Standing.false_of_pRank_le_two (hS : Standing G) (e : G ≃* H)
    (h : ∀ [Finite H] (r : ℕ), r.Prime → r ≠ 2 → Assembly.pRank r (⊤ : Subgroup H) ≤ 2) : False :=
  hS.false_of_localRank_le_two e fun r hr hr2 => localRank_le_of_pRank_le hr (h r hr hr2)

theorem Standing.false_of_card (hS : Standing G) (e : G ≃* H) {N : ℕ} (E : Finset ℕ)
    (hN : Nat.card H = N)
    (hE : ∀ [Finite H] (r : ℕ), r ∈ E → r.Prime → r ≠ 2 → localRank r H ≤ 2)
    (hcube : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ E → ¬ r ^ 3 ∣ N) : False := by
  refine hS.false_of_localRank_le_two e fun r hr hr2 => ?_
  by_cases hrE : r ∈ E
  · exact hE r hrE hr hr2
  · exact localRank_le_of_pRank_le hr (pRank_le_two_of_not_dvd hr (hN ▸ hcube r hr hr2 hrE))

end Transfer

theorem not_pow_three_dvd_of_primeFactors {N : ℕ} (hN : N ≠ 0) (S E : Finset ℕ)
    (hS : N.primeFactors = S) (h : ∀ p ∈ S, p = 2 ∨ p ∈ E ∨ ¬ p ^ 3 ∣ N) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ E → ¬ p ^ 3 ∣ N := by
  intro p hp hp2 hpE hdvd
  have hpN : p ∈ N.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans hdvd, hN⟩
  rw [hS] at hpN
  rcases h p hpN with h1 | h1 | h1
  · exact hp2 h1
  · exact hpE h1
  · exact h1 hdvd

section Entry

variable {G : Type} [Group G] [Finite G]

theorem isKGroup_of_isKProper_of_inCatalog (hsimple : IsSimpleGroup G) (hK : CFSG.Open.IsKProper G)
    (hC : InCatalog G) : CFSG.IsKGroup G := by
  have := hsimple
  exact CFSG.KCore.KProperNonab.kGroupAllSimple_of_isSimpleGroup inCatalog_isoInvariant
    inCatalog_containsAbelianSimple hC hK

theorem Standing.theoremThreeHyp (hS : Standing G) (hC : InCatalog G) :
    CFSG.RankThree.PartOne.Census3.TheoremThreeHyp G where
  isSimpleGroup := hS.simple
  nonabelian := hS.nonab
  kGroup := isKGroup_of_isKProper_of_inCatalog hS.simple hS.kProper hC
  twoLocalOddRank_le :=
    ((CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).symm.trans
      ((evenRank_eq_open G).trans hS.rank)).le

end Entry

end CFSG.LocalAnalysis.RankThreeUC
