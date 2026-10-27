module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityOriginal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentitySwap
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCountNative
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityIntegerExponent

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G] [Finite G]

theorem unique_two_involution_class_fixed_point_degree_identity
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hfaithful : ∀ g : G,
      (∀ x : pointRightCosetSpace H, pointRightCosetMul H x g = x) → g = 1)
    (hdouble : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (hodd : Odd (Nat.card (pointRightCosetSpace H)))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2)
    (huC : u ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer ({t} : Set G))
    (ht : t ∈ rightPairFlipFiber H z beta)
    (hno : ∀ E : Subgroup (pairPointStabilizer H beta),
      IsElementaryAbelian 2 E → Nat.card E ≠ 4)
    (htwo : ∀ v : G, orderOf v = 2 →
      v ∈ involutionPointClass u ∨ v ∈ involutionPointClass z)
    (hcentralizer : ∀ a b c d : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
      pointRightCosetMul H c u = c → pointRightCosetMul H d u = d →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) :
    let n := Nat.card (pointRightCosetSpace H)
    let k := Nat.card {x : pointRightCosetSpace H // pointRightCosetMul H x u = x}
    let D := pairPointStabilizer H beta
    let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
    let C := D ⊓ Subgroup.centralizer (V : Set G)
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let B := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let a : ℚ := (C.relIndex A : ℚ) / C.relIndex B
    3 ≤ k ∧ k < n ∧ Odd k ∧ Nat.card V = 4 ∧ IsElementaryAbelian 2 V ∧
      involutionPointClass u ≠ involutionPointClass z ∧
      Disjoint (involutionPointClass u) (involutionPointClass z) ∧
      {v | v ∈ involutionPointClass u ∧
        pointRightCosetMul H (rightCosetMk H 1) v = beta} = conjugacyWithin D (u * t) ∧
      (Nat.card (involutionPointClass u) : ℚ) =
        (n : ℚ) * ((n : ℚ) - 1) *
          (Subgroup.centralizer ({u} : Set G)).relIndex D /
          ((k : ℚ) * ((k : ℚ) - 1)) ∧
      (n : ℚ) - 1 = ((k : ℚ) - 1) * ((k : ℚ) * a + 1) ∧
      (∀ q i : ℤ, 2 ≤ q → 1 ≤ i → (k : ℚ) = (q : ℚ) ^ i + 1 →
        (n : ℚ) - 1 = (q : ℚ) ^ i * (((q : ℚ) ^ i + 1) * a + 1)) ∧
      (∀ (q : ℤ) (i : ℕ), 2 ≤ q → 1 ≤ i → (k : ℤ) = q ^ i + 1 →
        (n : ℚ) - 1 = (q : ℚ) ^ i * (((q : ℚ) ^ i + 1) * a + 1)) ∧
      (∀ q i : ℕ, 2 ≤ q → 1 ≤ i → k = q ^ i + 1 →
        (n : ℚ) - 1 = (q : ℚ) ^ i * (((q : ℚ) ^ i + 1) * a + 1)) := by
  have hgeometry := original_fixed_set_geometry_and_class_count
    h hfaithful hdouble hodd beta hbeta u t hu huC ht hcentralizer
  have hswap := original_two_class_swap_fiber h S hzS hzcenter beta hbeta
    u t hu huC ht hno htwo
  have hcount := original_degree_count_of_proved_swap_orbit
    H hdouble beta hbeta u t huC.1 hcentralizer hswap.1
  dsimp only at hgeometry hswap hcount ⊢
  obtain ⟨hk3, hkn, hkodd, hVcard, hVelem, hclasses, hdisjoint, hcard⟩ := hgeometry
  refine ⟨hk3, hkn, hkodd, hVcard, hVelem, hclasses, hdisjoint, hswap.1, hcard,
    hcount.2, ?_, ?_, ?_⟩
  · intro q i _ hi hk
    exact degree_identity_positive_integer_exponent _ _ _ hcount.2 q i hi hk
  · intro q i _ _ hk
    exact degree_identity_integer_power_substitution _ _ _ hcount.2 q i hk
  · intro q i _ _ hk
    exact degree_identity_power_substitution _ _ _ hcount.2 q i hk

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
