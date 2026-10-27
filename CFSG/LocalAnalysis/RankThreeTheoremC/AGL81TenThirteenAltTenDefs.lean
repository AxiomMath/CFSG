module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe (hatOf)

@[expose] def KFactFourSixTwo : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P J : Subgroup A) (t : A),
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    Open.pRank 3 Y ≤ 3 →
    J ≤ P → IsSubnormal (hatOf P J) ⊤ → Open.IsQuasisimple ↥(hatOf P J) →
    (∃ f : ↥(hatOf P J) →* alternatingGroup (Fin 5), Function.Surjective f) →
    t ∈ Subgroup.normalizer (Y : Set A) → t ∈ Subgroup.normalizer (P : Set A) →
    (∃ k : ℕ, t ^ 2 ^ k = 1) →
    hatOf P (J.map (MulAut.conj t).toMonoidHom) ≠ hatOf P J →
    hatOf P (J.map (MulAut.conj (t ^ 2)).toMonoidHom) = hatOf P J ∧
      ∃ j ∈ J, ∀ x ∈ J, t ^ 2 * x * (t ^ 2)⁻¹ * (j * x * j⁻¹)⁻¹ ∈ pCoreOf 2 P

@[expose] def KFactBlockAFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L I₀ : Subgroup G),
    Open.IsKGroup ↥X → Asc81bHyp X S → IsWeakSBlock X S L → ¬ InClassXBlock L →
    I₀ ∈ cZero (Subgroup.normalizer (S : Set G) ⊓ L) → IsTwoPrimeComponent I₀ I₀ →
    (∃ f : ↥I₀ →* alternatingGroup (Fin 5), Function.Surjective f) →
    (NineThreeTwo X S L ∨
      ∀ t ∈ X, t ∈ Subgroup.normalizer (S : Set G) → t ∈ Subgroup.normalizer (L : Set G) →
        t ∈ Subgroup.normalizer (I₀ : Set G)) ∧
    (Open.pRank 3 X ≤ 3 → ∀ t ∈ X, t ∈ Subgroup.normalizer (S : Set G) →
      (∃ k : ℕ, t ^ 2 ^ k = 1) → L.map (MulAut.conj t).toMonoidHom ≠ L →
        t ^ 2 ∈ Subgroup.normalizer (I₀ : Set G) ∧
          ∃ j ∈ I₀, ∀ x ∈ I₀, t ^ 2 * x * (t ^ 2)⁻¹ * (j * x * j⁻¹)⁻¹ ∈ pCoreOf 2 I₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
