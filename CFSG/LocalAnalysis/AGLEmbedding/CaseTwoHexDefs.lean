module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactBlockHexacode : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G),
    IsWeakSBlock M S L → NineThreeFour M S L →
    (∀ y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        (∃ k : ℕ, y ^ 3 ^ k = 1) →
        y ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
    (∀ l ∈ barM M L, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1) ∧
    (∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L → IsElemAbelian 3 E →
        Nat.card E ≤ 3 ^ 2) ∧
    ∃ χ : ↥(Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →*
        Multiplicative (ZMod 3),
      ∀ ζ (hζ : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))),
        ζ ∈ barM M L → ζ ≠ 1 → χ ⟨ζ, hζ⟩ ≠ 1

@[expose] def KFactBlockThreeASix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M L : Subgroup G),
    IsTwoPrimeComponent M L → Nat.card (Subgroup.center ↥(barM M L)) = 3 →
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) →
    (∀ y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        (∃ k : ℕ, y ^ 3 ^ k = 1) →
        y ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
    (∀ l ∈ barM M L, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1) ∧
    ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), T ≤ barM M L → IsPGroup 3 T →
      Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2)

end CFSG.AGLEmbedding
