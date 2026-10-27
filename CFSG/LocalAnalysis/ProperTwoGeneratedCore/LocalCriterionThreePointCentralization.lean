module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_three_point_normalized_subgroup_centralization
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (hcover : ∀ V : Subgroup G,
      Nonempty (V ≃* Multiplicative (ZMod 2 × ZMod 2)) →
        ∃ s ∈ V, s ∈ involutionPointClass z)
    (hhull : ∀ u : G, orderOf u = 2 → u ∉ involutionPointClass z →
      ∃ L : Subgroup G,
        L ≤ Subgroup.centralizer ({u} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
        (∃ s ∈ L, s ∈ involutionPointClass z) ∧
        (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
        (∀ a b : pointRightCosetSpace H,
          pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
            ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
        Group.IsSolvable (outerAutomorphismGroup L))
    (htriple : distinguishedTripleCentralization H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hswap : rightCosetTranslate H (rightCosetMk H 1) t = beta ∧
      rightCosetTranslate H beta t = rightCosetMk H 1)
    (X : Subgroup G) (hXD : X ≤ pairPointStabilizer H beta)
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (hthree : 3 ≤ Nat.card (pointFixedSet H X)) :
    ⁅X, Subgroup.zpowers t⁆ = ⊥ := by
  by_contra hnoncentral
  obtain ⟨p, hp, hpodd, P, _, _, _, _,
      ⟨W, hPW, hW, hWthree, hWmax⟩, hfree⟩ :=
    local_involution_point_three_point_noncentral_subgroup_class_free_maximal_prime_normalizer
      H z h S hzS hzcenter hdoubly htriple beta hbeta t htclass hswap X hXD hXnorm
      hnoncentral hthree
  have hempty := (hfree W hPW hW hWthree hWmax).2.1
  obtain ⟨s, hsnormalizer, hsclass⟩ :=
    local_involution_point_maximal_odd_prime_normalizer_meets_distinguished_class
      H z h S hzS hzcenter hdoubly hcover hhull p hp hpodd W hW hWthree hWmax
  have hmem : s ∈ (∅ : Set G) := hempty ▸ ⟨hsnormalizer, hsclass⟩
  exact hmem

end CFSG.ProperTwoGeneratedCore
