module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Defs

variable {G : Type} [Group G]

abbrev blockParabolic (M S L : Subgroup G) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
  barM M (Subgroup.normalizer (S : Set G) ⊓ L)

@[expose] def BlockInnerHyp (M S L : Subgroup G) : Prop :=
  ∀ l ∈ barM M L, (∀ s ∈ barM M S, ∃ s' ∈ barM M S, ∀ y ∈ barM M L,
      (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) →
    l ∈ blockParabolic M S L

end Defs

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsUThreeEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .twistedA 2 q

@[expose] def IsUFourTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA 3 q

@[expose] def IsUSixTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA 5 q

@[expose] def IsOmegaMinusTwoIndex (m : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedD m q

@[expose] def omegaMinusFlagIndex (m : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 4 m, (2 ^ j + 1) * (2 ^ (j - 1) - 1)

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockFiveParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → BlockInnerHyp M S L →
    (∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockParabolic M S L → ⁅W, W⁆ = W →
      Nat.Coprime 5 (Nat.card W)) →
    Nat.Coprime 5 (Nat.card (blockParabolic M S L))

@[expose] def KFactOutFiveCyclic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L E Q : Subgroup Y), IsComponentOf L ⊤ →
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) → E ≤ Subgroup.normalizer (L : Set Y) →
    IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
    E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥ →
    Q ≤ Subgroup.normalizer (L : Set Y) → Q ≤ Subgroup.normalizer (E : Set Y) →
    (∀ F : Subgroup Y, F ≤ E → Q ≤ Subgroup.normalizer (F : Set Y) → F = ⊥ ∨ F = E) → False

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockThreeOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockParabolic M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W)) →
    ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), U ≤ barM M (Subgroup.normalizer (S : Set G)) →
      U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup 3 U →
      (U ⊓ (barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))).relIndex
        U ≤ 3

@[expose] def KFactBlockNoSU38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → BlockInnerHyp M S L →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (V : Subgroup G), V ≤ M →
      O ≤ blockParabolic M S L → barM M V ≤ blockParabolic M S L →
      blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.Coprime 3 (Nat.card O) →
      blockParabolic M S L ≤ Subgroup.normalizer ((barM M V ⊔ O : Subgroup _) : Set _) →
      ⁅V, V⁆ = V → ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : V →* CatGroup d),
        IsUThreeEightIndex d → Function.Surjective ψ →
        3 ^ 7 ∣ Nat.card (blockParabolic M S L)

@[expose] def KFactBlockThreeOrderNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → BlockInnerHyp M S L →
    (∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockParabolic M S L → ⁅W, W⁆ = W →
      Nat.Coprime 3 (Nat.card W)) →
    (∀ Q : Sylow 3 (blockParabolic M S L), ¬ (IsCyclic (Q : Subgroup (blockParabolic M S L)) ∧
      Nat.card (Q : Subgroup (blockParabolic M S L)) = 9)) ∧
    ∀ u ∈ blockParabolic M S L, ∀ v ∈ blockParabolic M S L, orderOf u = 9 → orderOf v = 9 →
      u * v = v * u → ¬ Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockLeviU42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → BlockInnerHyp M S L →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (V : Subgroup G), V ≤ M →
      O ≤ blockParabolic M S L → barM M V ≤ blockParabolic M S L →
      blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.Coprime 3 (Nat.card O) →
      blockParabolic M S L ≤ Subgroup.normalizer ((barM M V ⊔ O : Subgroup _) : Set _) →
      (barM M V ⊔ O).relIndex (blockParabolic M S L) ≤ 2 →
      ⁅V, V⁆ = V → ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : V →* CatGroup d),
        IsUFourTwoIndex d → Function.Surjective ψ → Nat.Coprime 3 (Nat.card ψ.ker) →
        (∀ Q : Sylow 3 (blockParabolic M S L),
          Nat.card (Q : Subgroup (blockParabolic M S L)) = 3 ^ 4) →
        ¬ 3 ∣ Nat.card (Subgroup.center (barM M L)) →
        (∃ d : TauCeti.ValidLieTypeIndex, IsUSixTwoIndex d ∧ Nonempty (barM M L ≃* CatGroup d) ∧
            (blockParabolic M S L).relIndex (barM M L) = 693) ∨
          ∃ (m : ℕ) (d : TauCeti.ValidLieTypeIndex), 4 ≤ m ∧ IsOmegaMinusTwoIndex m d ∧
            Nonempty (barM M L ≃* CatGroup d) ∧
            (blockParabolic M S L).relIndex (barM M L) = omegaMinusFlagIndex m

@[expose] def KFactOmegaEightMinusAut : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsOmegaMinusTwoIndex 4 d →
    Nonempty (L ≃* CatGroup d) → ∀ Q : Subgroup (MulAut L), IsPGroup 3 Q → Nat.card Q ∣ 3 ^ 4

end CFSG.AGLEmbedding
