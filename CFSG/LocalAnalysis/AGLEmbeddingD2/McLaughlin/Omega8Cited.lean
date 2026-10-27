module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactOmega8Out : Prop :=
  (∀ (X : Type) [Group X] [Finite X] (Lb : Subgroup X), IsOmegaEightPlus ↥Lb → Lb.Normal →
    (Lb ⊔ Subgroup.centralizer (Lb : Set X)).index ∣ 6) ∧
  (∀ (X : Type) [Group X] [Finite X], Open.IsQuasisimple X →
    IsOmegaEightPlus (X ⧸ Subgroup.center X) → IsPGroup 2 (Subgroup.center X))

@[expose] def KFactOmega8Parabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Lb P : Subgroup X), IsOmegaEightPlus ↥Lb →
    IsParabolicTwo Lb P →
    Lb ⊓ Subgroup.normalizer (P : Set X) ≤ P ∧
    (¬ IsSylowTwoOf (pCoreOf 2 P) Lb →
      (∀ J : Subgroup X, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) → Open.pRank 3 P ≤ 2 →
      ∀ E : Subgroup X, E ≤ P → IsPGroup 3 E → IsElemAbelian 3 E ∧ Nat.card E ≤ 9) ∧
    (Open.pRank 3 P ≤ 1 → (∃ J : Subgroup X, J ≤ P ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J) →
      ∃ Y : Subgroup X, Y ≤ P ∧ (Y.subgroupOf P).Normal ∧
        IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∧
    (¬ IsSylowTwoOf (pCoreOf 2 P) Lb →
      (∀ J : Subgroup X, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) → Open.pRank 3 P ≤ 2 →
      ∀ E : Subgroup X, E ≤ P → IsElemAbelian 3 E → Nat.card E = 9 →
        ∃ E₁ : Subgroup X, E₁ ≤ E ∧ Nat.card E₁ = 3 ∧
          P ⊓ Subgroup.normalizer (E : Set X) ≤ Subgroup.normalizer (E₁ : Set X))

@[expose] def KFactOmega8Triality : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Lb P : Subgroup X), IsOmegaEightPlus ↥Lb → Lb.Normal →
    IsParabolicTwo Lb P → P ≠ Lb → ¬ IsSylowTwoOf (pCoreOf 2 P) Lb →
    (∃ u ∈ Subgroup.normalizer (P : Set X), IsPGroup 3 (Subgroup.zpowers u) ∧
      u ∉ Lb ⊔ Subgroup.centralizer (Lb : Set X)) →
    ∀ m : X, ∃ ℓ ∈ Lb,
      P.map (MulAut.conj m).toMonoidHom = P.map (MulAut.conj ℓ).toMonoidHom

@[expose] def KFactParabolicCoverOmega8 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (L S₀ A₁ A₂ : Subgroup W), IsOmegaEightPlus ↥L →
    IsSylowTwoOf S₀ L → CoveredByTwo L S₀ A₁ A₂ → Open.pRank 3 A₁ ≤ 2 → Open.pRank 3 A₂ ≤ 2 →
    (∃ J : Subgroup W, J ≤ A₁ ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J) ∨
      (∃ J : Subgroup W, J ≤ A₂ ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J)

@[expose] def KFactLThreeTwoOddIndex : Prop :=
  ∀ (N : Type) [Group N] [Finite N], Open.IsKGroup N → CharTwo (⊤ : Subgroup N) →
    ∀ N₀ : Subgroup N, GLBStronglyEmbedded 3 N₀ → Open.pRank 3 N₀ = 1 →
    ∀ Y : Subgroup N, Y ≤ N₀ → IsSubnormal Y N₀ → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) →
      ¬ 2 ∣ N₀.index

end CFSG.AGLEmbeddingD2.McLaughlin
