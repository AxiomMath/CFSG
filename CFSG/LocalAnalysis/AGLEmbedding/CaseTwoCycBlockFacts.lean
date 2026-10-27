module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

@[expose] def CitedBlockToralCycAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → p.Prime → 5 ≤ p →
    (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup p Q → IsCyclic Q) →
    ∀ u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      u ^ p = 1 → u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V) →
      (∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) →
      (∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          ζ ^ p = 1 → ζ = 1) ∧
        (u ∈ barM M L → ∀ v ∈ barM M L, v ^ p = 1 → v * u = u * v →
          v ∉ Subgroup.zpowers u →
          ∀ y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
            (∃ k : ℕ, y ^ p ^ k = 1) → y * v * y⁻¹ = v → y * u * y⁻¹ ≠ u * v)

@[expose] def CitedBlockToralThreeCyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q) →
    (∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ζ ^ 3 = 1 → ζ = 1) →
    ∀ u ∈ barM M L, u ^ 3 = 1 →
      u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        V ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V) →
      (∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) →
      ∀ v ∈ barM M L, v ^ 3 = 1 → v * u = u * v → v ∈ Subgroup.zpowers u

end CFSG.AGLEmbedding
