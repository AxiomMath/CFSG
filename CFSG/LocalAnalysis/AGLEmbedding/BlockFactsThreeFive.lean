module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

abbrev blockPL {G : Type} [Group G] (M S L : Subgroup G) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
  barM M (Subgroup.normalizer (S : Set G) ⊓ L)

@[expose] def KFactBlockCyclicThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y)) →
    Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))) →
    (∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L → IsElemAbelian 3 E →
      Nat.card E ≤ 3) →
    ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup 3 U →
      (U ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ≤ 3

@[expose] def KFactBlockThreeOneOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y)) →
    Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))) →
    Open.pRank 3 (blockPL M S L) ≤ 3 →
    IsMulCommutative ↥(CFSG.pCore 3
      (↥(blockPL M S L) ⧸ primeComplementCore (G := ↥(blockPL M S L)) 3)) →
    (∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), U ≤ blockPL M S L → IsPGroup 3 U →
      Nat.card U ≤ 3 ^ 3) ∧
    ((∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ blockPL M S L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 3) →
      ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        u ^ 3 ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        u ∉ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        2 ≤ Open.pRank 3 (barM M L ⊓ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M))))

@[expose] def KFactD4TwoGraphCentralizer : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (d : TauCeti.ValidLieTypeIndex),
    (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .D 4 q) →
    Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ α : MulAut J, α ^ 3 = 1 → α ∉ (MulAut.conj : J →* MulAut J).range →
      ∃ E : Subgroup J, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ∀ x ∈ E, α x = x

@[expose] def KFactBlockFiveNoncyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    5 ∣ Nat.card (blockPL M S L) →
    (∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2) ∧
    ∃ y ∈ barM M L, orderOf y = 3 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def KFactBlockThreeFives : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (J : Fin 3 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)),
      O ≤ blockPL M S L → blockPL M S L ≤ Subgroup.normalizer (O : Set _) →
      Nat.Coprime 5 (Nat.card O) →
      (∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), U ≤ blockPL M S L →
        ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V → IsSimpleGroup (U ⧸ V) →
          (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60) →
      (∀ i, J i ≤ blockPL M S L ∧ ∃ φ : ↥(J i) →* alternatingGroup (Fin 5),
        Function.Surjective φ ∧ ∀ x : ↥(J i), φ x = 1 ↔ (x : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ O) →
      (∀ i j, i ≠ j → ⁅J i, J j⁆ ≤ O) → 4 ≤ Open.pRank 3 (blockPL M S L)

@[expose] def CatalogOuterSolvable : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    Open.IsCatalogGroup S →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)

end CFSG.AGLEmbedding
