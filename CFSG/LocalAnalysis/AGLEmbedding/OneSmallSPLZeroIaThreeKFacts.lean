module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactBlockThreeCentCoprime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), CFSG.Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y)) →
    ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)), u ^ 3 = 1 →
      u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), D ≤ barM M L → ⁅D, D⁆ = D →
        D ≤ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → D = ⊥) →
      ∀ t ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        t ∈ Subgroup.centralizer ({u} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        Nat.Coprime 6 (orderOf t) →
        t ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def KFactSuzukiThreeCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) → Nat.Coprime 3 (Nat.card L) →
    ∀ u ∈ Subgroup.normalizer (L : Set Y), u ^ 3 = 1 → u ∉ Subgroup.centralizer (L : Set Y) →
      2 ∣ Nat.card (L ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y)

end CFSG.AGLEmbedding
