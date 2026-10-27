module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetLarge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetTwoPoint

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_maximal_prime_fixed_set_dichotomy
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (P : Subgroup G)
    (hP : IsPGroup p P) (hPH : P ≤ H)
    (hfixed : 2 ≤ Nat.card (pointFixedSet H P))
    (hmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → P ≤ Q →
      2 ≤ Nat.card (pointFixedSet H Q) → Q = P) :
    (∀ n : G, n ∈ Subgroup.normalizer (P : Set G) →
      ∀ a : pointRightCosetSpace H, a ∈ pointFixedSet H P →
        pointRightCosetMul H a n ∈ pointFixedSet H P) ∧
    (∀ a : pointRightCosetSpace H, a ∈ pointFixedSet H P →
      ∀ b : pointRightCosetSpace H, b ∈ pointFixedSet H P →
        ∃ n ∈ Subgroup.normalizer (P : Set G), pointRightCosetMul H a n = b) ∧
    (∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q →
      2 ≤ Nat.card (pointFixedSet H Q) → Q = P) ∧
    ((Nat.card (pointFixedSet H P) = 2 ∧
        ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
          ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) ∨
      (3 ≤ Nat.card (pointFixedSet H P) ∧
        ∃ r ∈ involutionPointClass z, r ∈ Subgroup.normalizer (P : Set G) ∧ r ∈ H)) ∧
    ¬ ((Nat.card (pointFixedSet H P) = 2 ∧
          ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
            ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) ∧
        (3 ≤ Nat.card (pointFixedSet H P) ∧
          ∃ r ∈ involutionPointClass z, r ∈ Subgroup.normalizer (P : Set G) ∧ r ∈ H)) := by
  have hlocal : IsLocallyMaximalTwoPointPrime H p P := hmax
  have hglobal := locally_maximal_is_globally_maximal h T hzT hzcenter p hp hP hPH hlocal
  refine ⟨fun _ hn _ ha => normalizer_preserves_pointFixedSet hn ha,
    locally_maximal_normalizer_transitive h T hzT hzcenter p hp hP hPH hlocal,
    hglobal, ?_, ?_⟩
  · by_cases htwo : Nat.card (pointFixedSet H P) = 2
    · exact Or.inl ⟨htwo,
        maximal_two_fixed_points_doubly_transitive h T hzT hzcenter p hp hodd hP hPH htwo hglobal⟩
    · have hthree : 3 ≤ Nat.card (pointFixedSet H P) := by omega
      exact Or.inr ⟨hthree, locally_maximal_large_fixed_set_class_normalizer_point
        h T hzT hzcenter p hp hP hPH hlocal hthree⟩
  · rintro ⟨⟨htwo, _⟩, hthree, _⟩
    omega

end CFSG.ProperTwoGeneratedCore
