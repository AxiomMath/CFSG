module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JZeroTwoHolds
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.HardMathSupport.Solomon.Proving.SU32Carrier
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

theorem IsSymThreeOrSUThreeTwo.three_dvd_card {Q : Type} [Group Q]
    (h : IsSymThreeOrSUThreeTwo Q) : 3 ∣ Nat.card Q := by
  rcases h with ⟨f⟩ | ⟨K, _, _, hK, ⟨f⟩⟩
  · rw [Nat.card_congr f.some.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := CFSG.HardMathSupport.Solomon.Proving.charP_two_of_card_four K hK
    have h2 := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 1)
      (by rw [hK]; norm_num)
    rw [Nat.card_congr f.toEquiv, pow_one] at *
    rw [h2]
    norm_num

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_oUpperTwo_of_symThree {I : Subgroup G}
    (hb : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) :
    3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 (IsSymThreeOrSUThreeTwo.three_dvd_card hb)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I) q
  obtain ⟨a, ha⟩ := exists_two_pow_mem_oUpperTwo y.2
  have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥I) (y ^ (2 ^ a))) = 3 := by
    rw [map_pow, Nat.Coprime.orderOf_pow (by rw [hq]; exact Nat.Coprime.pow_right a (by norm_num)),
      hq]
  have h1 : 3 ∣ orderOf (y ^ (2 ^ a)) := hord ▸ orderOf_map_dvd _ _
  have h4 := orderOf_dvd_natCard
    (⟨(y : G) ^ (2 ^ a), ha⟩ : ↥(CFSG.ComponentClassification.AS76b.oUpperTwo I))
  rw [Subgroup.orderOf_mk, ← Subgroup.coe_pow, Subgroup.orderOf_coe] at h4
  exact h1.trans h4

end CFSG.LocalAnalysis.RankThreeTheoremC
