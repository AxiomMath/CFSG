module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem triple_sylow_normalizer_not_le_original_point
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta)) :
    ¬ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) ≤ H := by
  let : Fact p.Prime := ⟨hp⟩
  let E := triplePointStabilizer H z beta
  let B := pairPointStabilizer H beta
  let F := oppositePairStabilizer H z beta
  let U : Subgroup G := (P : Subgroup E).map E.subtype
  have hUE : U ≤ E := Subgroup.map_subtype_le _
  have hUB : U ≤ B := hUE.trans inf_le_left
  have hUF : U ≤ F := hUE.trans (triple_stabilizer_le_opposite_pair H z beta)
  have hUp : IsPGroup p U := P.isPGroup'.map E.subtype
  by_cases hfull : ∃ R : Sylow p B, (R : Subgroup B).map B.subtype = U
  · obtain ⟨R, hR⟩ := hfull
    obtain ⟨r, hr, hrN, _⟩ := base_pair_specified_sylow_flip h S hzS hzcenter hbeta p hp R
    rw [hR] at hrN
    intro hNH
    exact pair_flip_not_mem_point hbeta hr (hNH hrN)
  · have hUinF : IsPGroup p (U.subgroupOf F) :=
      hUp.of_injective (Subgroup.subgroupOfEquivOfLe hUF).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hUF).injective
    obtain ⟨Q, hUQinternal⟩ := hUinF.exists_le_sylow
    let QA : Subgroup G := (Q : Subgroup F).map F.subtype
    have hUQ : U ≤ QA := by
      have hmap := Subgroup.map_mono (f := F.subtype) hUQinternal
      rwa [Subgroup.map_subgroupOf_eq_of_le hUF] at hmap
    have hUQstrict : U < QA := by
      apply lt_of_le_of_ne hUQ
      intro heq
      have hcard : Nat.card U = p ^ (Nat.card B).factorization p := by
        rw [heq, Subgroup.card_subtype, Q.card_eq_multiplicity,
          opposite_pair_order_eq_pair h S hzS hzcenter beta hbeta]
      exact hfull (p_subgroup_sylow_of_full_card p hp B U hUB hcard)
    have hQp : IsPGroup p QA := Q.isPGroup'.map F.subtype
    let R : Subgroup G := QA ⊓ Subgroup.normalizer (U : Set G)
    have hUR : U < R := pSubgroup_lt_normalizer_intersection p hp U QA hQp hUQstrict
    intro hNH
    have hRH : R ≤ H := inf_le_right.trans hNH
    have hRF : R ≤ F := inf_le_left.trans (Subgroup.map_subtype_le _)
    have hRE : R ≤ E := by
      intro r hr
      change r ∈ (rightCosetStabilizer H (rightCosetMk H 1) ⊓
        rightCosetStabilizer H beta) ⊓ rightCosetStabilizer H (rightCosetTranslate H beta z)
      rw [rightCosetStabilizer_base]
      exact ⟨⟨hRH hr, (hRF hr).1⟩, (hRF hr).2⟩
    have hRp : IsPGroup p R := hQp.of_injective
      (Subgroup.inclusion (show R ≤ QA from inf_le_left))
      (Subgroup.inclusion_injective _)
    have hbound := p_subgroup_card_le_prime_part p hp E R hRE hRp
    have hcardU : Nat.card U = p ^ (Nat.card E).factorization p := by
      rw [Subgroup.card_subtype, P.card_eq_multiplicity]
    rw [← hcardU] at hbound
    exact (not_lt_of_ge hbound) (Subgroup.card_lt_of_lt hUR)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
