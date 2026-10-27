module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthPrimePart

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

variable {G : Type*} [Group G] [Finite G]

theorem normal_subgroup_image_sylow_intersection
    (p : ℕ) (hp : p.Prime) (B : Subgroup G) (D : Subgroup B) [D.Normal]
    (Q : Sylow p B) :
    ∃ R : Sylow p (D.map B.subtype),
      (R : Subgroup (D.map B.subtype)).map (D.map B.subtype).subtype =
        (Q : Subgroup B).map B.subtype ⊓ D.map B.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  let J := D.map B.subtype
  let e : D ≃* J := D.equivMapOfInjective B.subtype B.subtype_injective
  obtain ⟨R, hR⟩ := generatedPairGrowth_sylow_intersection_normal hp D Q
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  let R' : Sylow p J := R.mapSurjective (f := e.toMonoidHom) hf
  have hcomp : J.subtype.comp e.toMonoidHom = B.subtype.comp D.subtype := by
    ext a
    rfl
  refine ⟨R', ?_⟩
  dsimp only [R']
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, ← Subgroup.map_map, hR,
    Subgroup.map_inf _ _ _ B.subtype_injective]

theorem normal_image_intersection_full_prime_part
    (p : ℕ) (hp : p.Prime) (B : Subgroup G) (D : Subgroup B) [D.Normal]
    (E : Subgroup G) (Q : Sylow p B)
    (hQE : (Q : Subgroup B).map B.subtype ≤ E) :
    (Nat.card (D.map B.subtype ⊓ E : Subgroup G)).factorization p =
      (Nat.card (D.map B.subtype)).factorization p := by
  obtain ⟨R, hR⟩ := normal_subgroup_image_sylow_intersection p hp B D Q
  apply generatedPairGrowth_full_prime_part_of_sylow_contained hp _ _ inf_le_left R
  rw [hR]
  exact le_inf inf_le_right (inf_le_left.trans hQE)

theorem sylow_extension_of_equal_prime_parts
    (p : ℕ) (hp : p.Prime) (J V : Subgroup G) (hVJ : V ≤ J)
    (hpart : (Nat.card V).factorization p = (Nat.card J).factorization p)
    (P : Sylow p V) :
    ∃ R : Sylow p J, (R : Subgroup J).map J.subtype = (P : Subgroup V).map V.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  apply p_subgroup_sylow_of_full_card p hp J ((P : Subgroup V).map V.subtype)
    ((Subgroup.map_subtype_le _).trans hVJ)
  rw [Subgroup.card_subtype, P.card_eq_multiplicity, hpart]

theorem triple_odd_core_full_prime_parts_in_both_pairs
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (hcontains : ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    let V := (CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    (Nat.card V).factorization p = (Nat.card (pairOddCore H beta)).factorization p ∧
      (Nat.card V).factorization p = (Nat.card (oppositePairOddCore H z beta)).factorization p := by
  dsimp only
  constructor
  · obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
    obtain ⟨Q, hQ⟩ := hcontains
    exact generatedPairGrowth_triple_odd_core_full_prime_part h S hzS hzcenter hbeta ht hp Q hQ
  · obtain ⟨Q, hQ⟩ := triple_contains_opposite_pair_sylow h S hzS hzcenter beta hbeta p hp hcontains
    rw [triple_odd_core_eq_opposite_pair_intersection h S hzS hzcenter beta hbeta]
    exact normal_image_intersection_full_prime_part p hp
      (oppositePairStabilizer H z beta) (CFSG.oddCore (oppositePairStabilizer H z beta))
      (triplePointStabilizer H z beta) Q hQ

theorem triple_odd_core_sylow_full_in_both_pairs
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (hcontains : ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype)) :
    (∃ R : Sylow p (pairOddCore H beta),
      (R : Subgroup (pairOddCore H beta)).map (pairOddCore H beta).subtype =
        (P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype) ∧
      ∃ R : Sylow p (oppositePairOddCore H z beta),
        (R : Subgroup (oppositePairOddCore H z beta)).map (oppositePairOddCore H z beta).subtype =
          (P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype)).map
            ((CFSG.oddCore (triplePointStabilizer H z beta)).map
              (triplePointStabilizer H z beta).subtype).subtype := by
  obtain ⟨hBpart, hFpart⟩ := triple_odd_core_full_prime_parts_in_both_pairs
    h S hzS hzcenter beta hbeta p hp hcontains
  constructor
  · apply sylow_extension_of_equal_prime_parts p hp _ _ _ hBpart P
    rw [triple_odd_core_eq_pair_intersection h S hzS hzcenter beta hbeta]
    exact inf_le_left
  · apply sylow_extension_of_equal_prime_parts p hp _ _ _ hFpart P
    rw [triple_odd_core_eq_opposite_pair_intersection h S hzS hzcenter beta hbeta]
    exact inf_le_left

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
