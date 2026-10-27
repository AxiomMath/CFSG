module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWTwo
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer


theorem l34TSylowWStep_of_certs (hMax : MaximalTwoComponentInput) :
    ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
      (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
      IsThreeConnected (S ⊓ withKernel J) →
      ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
        (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
        normalizer (J : Set G) ≤ normalizer (W : Set G) →
        ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
          IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
          IsL34Type (K ⧸ Open.fusionZStar K) →
          (J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) ∨
            (conjugate K a ≠ K ∧ J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G)))) →
        ∀ T : Subgroup G, IsSylowTwoIn T (normalizer (W : Set G)) → S ≤ T →
          (∀ e ∈ T, ∀ e' ∈ T, conjugate K e = K ∨ conjugate K e' = K ∨
            conjugate K e = conjugate K e') →
          (T ⊓ zStarIn K = ⊥ ∨ T ≤ normalizer (K : Set G)) →
          ∀ F : Subgroup G, F ≤ T → IsEightGroup F →
            (∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) → wGroup F = W := by
  intro G _ _ a x J S A hset hcent hZa _ _ W _ _ hWB hNJ K hKM hKc hKL hout T hT hST hTK hH3 F
    hFT hF hns
  by_cases hZK : T ⊓ zStarIn K = ⊥
  · exact wGroup_eq_of_inf_zStarIn_eq_bot hset hWB hNJ hKM hKc hKL hout hT hST hTK hZK hFT hF
      hns
  · exact wGroup_eq_of_le_normalizer_of_inf_zStarIn_ne_bot hMax hset hcent hZa hWB hNJ hKM hKc
      hKL hout hT hST (hH3.resolve_left hZK) hZK hFT hF hns

end CFSG.ComponentClassification.GrSLit.GrS5S
