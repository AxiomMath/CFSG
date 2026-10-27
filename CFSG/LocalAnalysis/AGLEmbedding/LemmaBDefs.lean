module

public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def PerfectCyclicSylow {X : Type*} [Group X] (p : ℕ) (J : Subgroup X) : Prop :=
  ∀ V : Subgroup X, V ≤ J → ⁅V, V⁆ = V → ∀ A : Subgroup X, A ≤ V → IsPGroup p A → IsCyclic A

@[expose] def KFactParabolicAutomizerCyc : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L J U : Subgroup X) (y : X) (p r : ℕ),
    IsComponentOf L ⊤ → IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J →
    p.Prime → p ≠ 2 → PerfectCyclicSylow p J →
    U ≤ Subgroup.normalizer (L : Set X) → U ≤ Subgroup.normalizer (J : Set X) → IsPGroup p U →
    y ∈ Subgroup.normalizer (L : Set X) → y ∈ Subgroup.normalizer (J : Set X) →
    y ∈ Subgroup.normalizer (U : Set X) →
    r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p → ¬ r ∣ p - 1 →
    ∃ n : ℕ, ¬ r ∣ n ∧ ∀ u ∈ U, y ^ n * u * (y ^ n)⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set X)

@[expose] def KFactAltSixSevenAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L U : Subgroup X) (p : ℕ), IsComponentOf L ⊤ →
    (Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥L ≃* alternatingGroup (Fin 7))) →
    p.Prime → p ≠ 2 → U ≤ Subgroup.normalizer (L : Set X) → IsPGroup p U →
    (U ⊓ Subgroup.centralizer (L : Set X)).relIndex U ≤ p ^ 2

@[expose] def CitedBlockTransvectionCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → p.Prime → p ≠ 2 →
    PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ U : Subgroup G, U ≤ M ⊓ Subgroup.normalizer (S : Set G) →
      U ≤ Subgroup.normalizer (L : Set G) → IsPGroup p U →
      ∃ u ∈ U, ∀ x ∈ U, ∃ k : ℕ, x * (u ^ k)⁻¹ ∈ blockCentralizer M L

@[expose] def CitedBlockAltNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    (NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) → p.Prime → p ≠ 2 →
    PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ U : Subgroup G, U ≤ M ⊓ Subgroup.normalizer (S : Set G) →
      U ≤ Subgroup.normalizer (L : Set G) → IsPGroup p U →
      (U ⊓ blockCentralizer M L).relIndex U ≤ p ^ 2

end CFSG.AGLEmbedding
