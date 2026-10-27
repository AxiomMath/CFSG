module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem normalizing_p_subgroup_has_nonbase_fixed_point
    (H U Q : Subgroup G) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hQ : IsPGroup p Q) (hQN : Q ≤ Subgroup.normalizer (U : Set G))
    (hcount : Nat.card (pointFixedSet H U) ≡ 2 [MOD p]) :
    ∃ delta : pointRightCosetSpace H,
      delta ∈ pointFixedSet H U ∧ delta ∈ pointFixedSet H Q ∧
        delta ≠ rightCosetMk H 1 := by
  have hmod : Nat.card
      (pointFixedSet H U ∩ pointFixedSet H Q : Set (pointRightCosetSpace H)) ≡ 2 [MOD p] :=
    (pointFixedSet_restricted_card_modEq p hp H U Q hQ hQN).symm.trans hcount
  have htwo := two_le_of_modEq_two p _ hp hodd hmod
  by_contra hnone
  have hsubset :
      pointFixedSet H U ∩ pointFixedSet H Q ⊆ ({rightCosetMk H 1} : Set (pointRightCosetSpace H)) := by
    intro delta hdelta
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact hnone ⟨delta, hdelta.1, hdelta.2, hne⟩
  have hcard := Set.ncard_le_ncard hsubset
  simp only [Set.ncard_singleton] at hcard
  change Nat.card
    (pointFixedSet H U ∩ pointFixedSet H Q : Set (pointRightCosetSpace H)) ≤ 1 at hcard
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerNoncentral
