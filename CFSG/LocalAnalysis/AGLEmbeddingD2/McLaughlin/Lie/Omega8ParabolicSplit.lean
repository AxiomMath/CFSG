module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8ParabolicBasic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactOmega8ParabolicL32 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Lb P : Subgroup X), IsOmegaEightPlus ↥Lb →
    IsParabolicTwo Lb P →
    Open.pRank 3 P ≤ 1 → (∃ J : Subgroup X, J ≤ P ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J) →
      ∃ Y : Subgroup X, Y ≤ P ∧ (Y.subgroupOf P).Normal ∧
        IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)

@[expose] def KFactOmega8ParabolicLines : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Lb P : Subgroup X), IsOmegaEightPlus ↥Lb →
    IsParabolicTwo Lb P →
    ¬ IsSylowTwoOf (pCoreOf 2 P) Lb →
      (∀ J : Subgroup X, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) → Open.pRank 3 P ≤ 2 →
      ∀ E : Subgroup X, E ≤ P → IsElemAbelian 3 E → Nat.card E = 9 →
        ∃ E₁ : Subgroup X, E₁ ≤ E ∧ Nat.card E₁ = 3 ∧
          P ⊓ Subgroup.normalizer (E : Set X) ≤ Subgroup.normalizer (E₁ : Set X)

theorem kFactOmega8Parabolic_of_parts (h3 : KFactOmega8ParabolicL32)
    (h4 : KFactOmega8ParabolicLines) : KFactOmega8Parabolic := fun X _ _ Lb P hΩ hP =>
  ⟨Lie.omega8_parabolic_le hΩ hP, Lie.omega8_parabolic_elemAbelian hΩ hP, h3 X Lb P hΩ hP,
    h4 X Lb P hΩ hP⟩

end CFSG.AGLEmbeddingD2.McLaughlin
