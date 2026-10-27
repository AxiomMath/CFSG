module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerFixedCosets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

variable {G : Type*} [Group G]

theorem normalizer_point_index_eq_fixed_set_card
    (H U : Subgroup G) (hUH : U ≤ H)
    (htrans : ∀ a b : pointRightCosetSpace H, a ∈ pointFixedSet H U →
      b ∈ pointFixedSet H U →
      ∃ n : G, n ∈ Subgroup.normalizer (U : Set G) ∧ pointRightCosetMul H a n = b) :
    (H.subgroupOf (Subgroup.normalizer (U : Set G))).index =
      Nat.card (pointFixedSet H U) := by
  rw [← pointRightCosetSpace_card_eq_index]
  exact Nat.card_congr (normalizerRightCosetFixedEquiv H U hUH htrans)

theorem residue_two_subgroup_sylow_promotes [Finite G]
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (B : Subgroup G)
    (hindex : B.index ≡ 2 [MOD p]) (Q : Sylow p B) :
    ∃ R : Sylow p G, (R : Subgroup G) = (Q : Subgroup B).map B.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : ¬ p ∣ 2 := by
    intro hdvd
    have heq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hp.ne_one
    rw [heq] at hodd
    norm_num at hodd
  have hnot : ¬ p ∣ B.index := by
    intro hdvd
    exact hp2 (Nat.modEq_zero_iff_dvd.mp
      (hindex.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
  let W : Subgroup G := (Q : Subgroup B).map B.subtype
  have hWp : IsPGroup p W := Q.isPGroup'.map _
  have hWi : ¬ p ∣ W.index := by
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul Q.not_dvd_index hnot
  exact ⟨hWp.toSylow hWi, IsPGroup.toSylow_coe hWp hWi⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral
