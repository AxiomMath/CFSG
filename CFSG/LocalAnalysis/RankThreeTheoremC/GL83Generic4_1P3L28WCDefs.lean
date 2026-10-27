module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Shape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def L28SylowInversion : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL28 K → ∀ T : Sylow 3 K,
    ∃ n ∈ normalizer ((T : Subgroup K) : Set K),
      ∀ t ∈ (T : Subgroup K), t ^ 3 = 1 → n * t * n⁻¹ = t⁻¹

@[expose] def L28Prop34NoWC (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (J : Subgroup G) (x : G) : Prop :=
  (P : Subgroup G) ≤ centralizer ({x} : Set G) ∧ Nat.card (L28Z (P : Subgroup G)) = p ^ 2 ∧
  (∀ t ∈ (P : Subgroup G) ⊓ J, t ^ p = 1 → t ∈ L28Z (P : Subgroup G)) ∧
  (∀ u ∈ (P : Subgroup G), u ^ p = 1 → u ∉ L28Z (P : Subgroup G) → L28OuterOn J u)

@[expose] def L28Prop34SNoWC (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (J : Subgroup G) (x : G) : Prop :=
  L28Prop34NoWC p P J x ∧ L28Shape p (P : Subgroup G)

@[expose] def GL83GenericPrimeThreeL28Prop34SNoWC (G : Type) [Group G] [Finite G] : Prop :=
  GenericL28At G fun p P _ x J => L28Prop34SNoWC p P J x

end CFSG.LocalAnalysis.RankThreeTheoremC
