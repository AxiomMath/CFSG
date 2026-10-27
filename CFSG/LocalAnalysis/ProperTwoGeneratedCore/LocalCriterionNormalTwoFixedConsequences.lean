module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedSylows

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem normal_two_hull_all_sylow_fixed_points
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q) :
    Odd (Nat.card (conjugacyWithin H z)) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card (conjugacyWithin H z) →
        (∀ P : Sylow p G, Nat.card (pointFixedSet H (P : Subgroup G)) = 2 ∧
          ∃ lambda mu : pointRightCosetSpace H, lambda ≠ mu ∧
            pointFixedSet H (P : Subgroup G) = {lambda, mu}) ∧
        ∀ lambda mu : pointRightCosetSpace H, lambda ≠ mu →
          ∀ P : Sylow p (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G),
            (∃ T : Sylow p G, (T : Subgroup G) =
              (P : Subgroup (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G)).map
                (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G).subtype) ∧
              pointFixedSet H
                ((P : Subgroup (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G)).map
                  (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G).subtype) =
                {lambda, mu} := by
  refine ⟨point_subgroup_full_class_card_odd h S hzS hzcenter, ?_⟩
  intro p hp hdiv
  refine ⟨?_, ?_⟩
  · intro P
    exact ⟨every_ambient_sylow_fixed_card_two h S hzS hzcenter hQH hQnormal hQtwo hzQ p hp hdiv P,
      every_ambient_sylow_whole_two_fixed_set h S hzS hzcenter hQH hQnormal hQtwo hzQ p hp hdiv P⟩
  · intro lambda mu hne P
    exact pair_sylow_ambient_and_whole_fixed_set h S hzS hzcenter hQH hQnormal hQtwo hzQ
      p hp hdiv lambda mu hne P

theorem normal_two_hull_has_base_pair_maximal_sylow
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (hm : 1 < Nat.card (conjugacyWithin H z)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (conjugacyWithin H z) ∧
      ∃ P : Sylow p G, (P : Subgroup G) ≤ H ∧
        (∃ beta : pointRightCosetSpace H, beta ≠ rightCosetMk H 1 ∧
          pointFixedSet H (P : Subgroup G) = {rightCosetMk H 1, beta}) ∧
        ∀ A : Subgroup G, IsPGroup p A → (P : Subgroup G) ≤ A → A = (P : Subgroup G) := by
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (by omega : Nat.card (conjugacyWithin H z) ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have hodd := (prime_dividing_point_class_odd_part_gt_one h S hzS hzcenter p hp hdiv).1
  obtain ⟨g, hgH⟩ : ∃ g : G, g ∉ H := by
    by_contra hnone
    apply h.proper
    apply top_unique
    intro g _
    by_contra hgH
    exact hnone ⟨g, hgH⟩
  let beta := rightCosetMk H g
  have hbeta : beta ≠ rightCosetMk H 1 := by
    intro heq
    apply hgH
    apply (point_right_base_fixed_iff H g).mp
    rw [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul]
    exact heq
  let B := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta
  let R : Sylow p B := default
  obtain ⟨⟨P, hP⟩, hpair⟩ := pair_sylow_ambient_and_whole_fixed_set
    h S hzS hzcenter hQH hQnormal hQtwo hzQ p hp hdiv (rightCosetMk H 1) beta hbeta.symm R
  have hPH : (P : Subgroup G) ≤ H := by
    rw [hP]
    have hh : (R : Subgroup B).map B.subtype ≤ rightCosetStabilizer H (rightCosetMk H 1) :=
      (Subgroup.map_subtype_le (R : Subgroup B)).trans inf_le_left
    rwa [rightCosetStabilizer_base] at hh
  rw [← hP] at hpair
  exact ⟨p, hp, hodd, hdiv, P, hPH, ⟨beta, hbeta, hpair⟩, fun A hA hPA => P.is_maximal' hA hPA⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
