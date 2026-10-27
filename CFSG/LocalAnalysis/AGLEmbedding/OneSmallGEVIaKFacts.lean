module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactU33SylowInvert : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSmallUnitary 3 K → ∀ T : Sylow 3 K,
    ∀ t ∈ (T : Subgroup K), t ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n * t * n⁻¹ = t⁻¹

@[expose] def CitedBlockThreeAutNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y)) →
    ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)), u ^ 3 = 1 →
      u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L) →
      ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup 3 U →
        (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 9

@[expose] def KFactFi22AltSection : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsFi22 L →
    ∃ (n : ℕ) (J : Subgroup L), 9 ≤ n ∧ Nonempty (J ≃* alternatingGroup (Fin n))

end CFSG.AGLEmbedding
