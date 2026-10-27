module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def CitedBlockToralCenterFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q) →
    ¬ (Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))) →
    ∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ζ ^ 3 = 1 → ζ ≠ 1 →
    ∀ u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      u ^ 3 = 1 → u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) →
      ∀ X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsPGroup 3 X →
        X ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        X ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        X ≤ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → Nat.card X ≤ 3 ^ 4 →
        (∀ Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsPGroup 3 Y →
          Y ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          Y ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          Y ≤ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          Nat.card Y ≤ Nat.card X) →
        ⁅X, X⁆ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ∀ e ∈ ⁅X, X⁆, e ∈ barM M L → e ^ 3 = 1 → e = 1

end CFSG.HardMathSupport.Curtis.Coordinator
