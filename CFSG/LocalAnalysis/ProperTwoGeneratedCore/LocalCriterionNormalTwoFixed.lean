module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedConsequences
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetDoubleTransitivity

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_normal_two_hull_sylow_fixed_points
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q) :
    Odd (Nat.card (conjugacyWithin H z)) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card (conjugacyWithin H z) →
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
                {lambda, mu}) ∧
      (1 < Nat.card (conjugacyWithin H z) →
        ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
          ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) := by
  have hfixed := normal_two_hull_all_sylow_fixed_points
    h S hzS hzcenter hQH hQnormal hQtwo hzQ
  refine ⟨hfixed.1, hfixed.2, ?_⟩
  intro hm
  obtain ⟨p, hp, _, hdiv, P, hPH, ⟨beta, _, hPfixed⟩, _⟩ :=
    normal_two_hull_has_base_pair_maximal_sylow
      h S hzS hzcenter hQH hQnormal hQtwo hzQ hm
  let : Fact p.Prime := ⟨hp⟩
  apply LocalCriterionMaximalFixedSet.point_right_doubly_transitive_of_base_pair_sylows
    H p hp P hPH beta hPfixed
  intro b hb
  let B := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H b
  let R : Sylow p B := default
  obtain ⟨⟨T, hT⟩, _⟩ := pair_sylow_ambient_and_whole_fixed_set
    h S hzS hzcenter hQH hQnormal hQtwo hzQ p hp hdiv
      (rightCosetMk H 1) b hb.symm R
  refine ⟨T, ?_⟩
  rw [hT]
  have hRB : (R : Subgroup B).map B.subtype ≤ B := Subgroup.map_subtype_le _
  simpa only [B, rightCosetStabilizer_base] using hRB

end CFSG.ProperTwoGeneratedCore
