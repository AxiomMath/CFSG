module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def NormalizerExponent (p : ℕ) {X : Type*} [Group X] (D : Subgroup X) : Prop :=
  ∀ x ∈ normalizer (D : Set X), (∃ k : ℕ, x ^ p ^ k = 1) → x ^ p = 1

structure ZJFrame (p : ℕ) {Y : Type} [Group Y] [Finite Y] (K D V : Subgroup Y) [K.Normal] :
    Prop where
  pre : ThompsonPreFrame p K D
  exists_component : ∃ L : Subgroup (Y ⧸ K), CFSG.IsComponent L ∧
    p ∣ Nat.card (L ⧸ center L) ∧ IsCatalogGroup (L ⧸ center L)
  sections : CFSG.AGLEmbedding.CatalogSimpleSections Y
  rank3 : ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3
  charTwo : centralizer (CFSG.pCore 2 Y : Set Y) ≤ CFSG.pCore 2 Y
  sylow2 : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 Y) K
  V_two : IsPGroup 2 V
  D_norm : D ≤ normalizer (V : Set Y)
  core_le : CFSG.pCore 2 Y ≤ V
  noncover : ∀ Z : Subgroup Y, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
    ¬ p ∣ Nat.card (invariantTwoJoinIn D (normalizer (Z : Set Y)))
  exp : NormalizerExponent p D

@[expose] def KFactZJFactorization : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
    CFSG.AGLEmbedding.CatalogSimpleSections X →
    centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    (∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3) →
    ∀ K : Subgroup X, K.Normal → CFSG.IsPComponent p K →
    (∃ T : Sylow 2 X, K ⊔ (T : Subgroup X) = ⊤) →
    ¬ 3 ∣ Nat.card (⁅K, (CFSG.pPrimeCore p K).map K.subtype⁆ : Subgroup X) →
    (∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal) →
    ∀ S : Subgroup X, IsPGroup 2 S → CFSG.pCore 2 X ≤ S →
    (∀ Z : Subgroup X, Z ≤ S → Z ≠ ⊥ → (Z.subgroupOf S).Characteristic →
      ¬ K ≤ normalizer (Z : Set X) ⊔ CFSG.pPrimeCore p X) →
    IsChevTwo ((↥K ⧸ CFSG.pPrimeCore p ↥K) ⧸ center (↥K ⧸ CFSG.pPrimeCore p ↥K)) ∨
      ∃ n : ℕ, Nonempty ((↥K ⧸ CFSG.pPrimeCore p ↥K) ⧸ center (↥K ⧸ CFSG.pPrimeCore p ↥K) ≃*
        alternatingGroup (Fin n))

@[expose] def KFactAlmostSimpleRankTwo : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
      (∀ P : Sylow p (X ⧸ L), (P : Subgroup (X ⧸ L)).Normal) ∧
      (IsChevTwo L → ∀ D : Subgroup X, ThompsonFrame p D → NormalizerExponent p D →
        p ∣ Nat.card (invariantTwoJoinIn D L) → False)

end CFSG.LocalAnalysis.RankThreeTheoremC
