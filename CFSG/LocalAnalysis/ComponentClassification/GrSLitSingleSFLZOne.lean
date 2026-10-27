module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFL
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4DiagMem
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

@[expose] def L34Lemma43ZOneStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    S ⊓ zStarIn J = ⊥ →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        (J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) ∨
          (conjugate K a ≠ K ∧ J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G)))) →
        normalizer (W : Set G) ≤ normalizer (K : Set G)

end CFSG.ComponentClassification.GrSLit
