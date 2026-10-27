module

public import CFSG.LocalAnalysis.QuasithinUnique.FusionDatum

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsComponentIn (L H : Subgroup G) : Prop :=
  L ≤ H ∧ CFSG.IsComponent (L.subgroupOf H)

@[expose] def omegaOne (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ P ∧ x ^ 2 = 1}

@[expose] def LocalComponentRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M U : Subgroup G) (z : G),
    UniqueFusionDatum T M U z → ∀ u ∈ U, u ≠ 1 →
    ¬ Subgroup.centralizer ({u} : Set G) ≤ M →
    ∀ S : Subgroup G, IsSylowTwoOf S (Subgroup.centralizer ({u} : Set G)) → U ≤ S →
    ∀ L : Subgroup G, IsComponentIn L (Subgroup.centralizer ({u} : Set G)) →
      IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ fusionIsBenderGroup L ∧
      U ≤ Subgroup.normalizer (L : Set G) ∧
      U ⊓ L = omegaOne (S ⊓ L) ∧ 4 ≤ Nat.card ↥(U ⊓ L) ∧
      (U ⊓ L) ⊔ (U ⊓ Subgroup.centralizer (L : Set G)) = U ∧
      (U ⊓ L) ⊓ (U ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G) ≤ M ∧
      (∀ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G),
        ∀ c ∈ U ⊓ Subgroup.centralizer (L : Set G), n⁻¹ * c * n = c) ∧
      (∀ a ∈ U ⊓ L, ∀ b ∈ U ⊓ L, a ≠ 1 → b ≠ 1 →
        ∃ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G), n⁻¹ * a * n = b) ∧
      (∀ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G), ∀ a ∈ U ⊓ L, a ≠ 1 →
        n⁻¹ * a * n = a → ∀ x ∈ U, n⁻¹ * x * n = x) ∧
      (∃ g ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G),
        ∀ n ∈ L ⊓ Subgroup.normalizer ((U ⊓ L : Subgroup G) : Set G), ∃ k : ℕ,
          ∀ x ∈ U, n⁻¹ * x * n = (g ^ k)⁻¹ * x * g ^ k)

@[expose] def ComponentEmbeddingUnderInvolution : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M U : Subgroup G) (z : G),
    UniqueFusionDatum T M U z → ∀ v ∈ U, v ≠ 1 →
    CFSG.oddCore (Subgroup.centralizer ({v} : Set G)) = ⊥ →
    (∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({v} : Set G)) →
      U ≤ Subgroup.normalizer (K : Set G)) →
    ∀ u ∈ U, ∀ L : Subgroup G,
      IsComponentIn L (Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) →
      ∃ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({v} : Set G)) ∧ L ≤ K

end CFSG.QuasithinUnique
