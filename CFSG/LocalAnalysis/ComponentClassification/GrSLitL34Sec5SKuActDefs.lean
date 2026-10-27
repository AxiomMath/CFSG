module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34KuActionAt (P : ∀ (G : Type) [Group G], Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J Y : Subgroup G), GSUnbalancingTriple a x J →
    P G J → Odd (Nat.card Y) → Y ≤ normalizer (J : Set G) → Y ≤ centralizer ({x} : Set G) →
    ¬ ⁅J, Y⁆ ≤ oddIn J → ¬ ⁅J ⊓ centralizer ({x} : Set G), Y⁆ ≤ oddIn J

@[expose] def L34KuActionL25 : Prop :=
  L34KuActionAt fun _ _ J => IsL2Type 5 (J ⧸ pPrimeCore 2 J)

@[expose] def L34KuActionL27 : Prop :=
  L34KuActionAt fun _ _ J => IsL2Type 7 (J ⧸ pPrimeCore 2 J)

@[expose] def L34KuActionL34 : Prop :=
  L34KuActionAt fun _ _ J => IsL34Type (J ⧸ Open.fusionZStar J)

end CFSG.ComponentClassification.GrSLit.GrS5S
