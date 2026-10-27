module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsL33U35L37HeOrder (n : ℕ) : Prop :=
  n = 5616 ∨ n = 126000 ∨ n = 1876896 ∨ n = 4030387200

@[expose] def NoL33U35L37HeAt {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) : Prop :=
  ∀ (O W : Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
    Nat.Coprime 3 (Nat.card O) → W ≤ P →
    P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y) → ⁅W, W⁆ = W →
    ∀ (U : Type) [Group U] [Finite U] [IsSimpleGroup U] (ψ : ↥W →* U),
      Function.Surjective ψ → ¬ IsL33U35L37HeOrder (Nat.card U)

@[expose] def KFactCompParabNoL33U35L37He : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P → NoL33U35L37HeAt P

@[expose] def KFactCompParabNoL33U35L37HeOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → NoL33U35L37HeAt P

@[expose] def KFactBlockNoL33U35L37He : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (V : Subgroup G), V ≤ M →
      O ≤ blockParabolic M S L → barM M V ≤ blockParabolic M S L →
      blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.Coprime 3 (Nat.card O) →
      blockParabolic M S L ≤ Subgroup.normalizer ((barM M V ⊔ O : Subgroup _) : Set _) →
      ⁅V, V⁆ = V → ∀ (U : Type) [Group U] [Finite U] [IsSimpleGroup U] (ψ : ↥V →* U),
        Function.Surjective ψ → ¬ IsL33U35L37HeOrder (Nat.card U)

end CFSG.AGLEmbedding
