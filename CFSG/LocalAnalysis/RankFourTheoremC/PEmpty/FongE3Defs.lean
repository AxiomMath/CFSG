module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

@[expose] def KFactP65RankThreeAt (A : Type) [Group A] [Finite A] : Prop :=
  ∀ (p : ℕ) (X Y Q B : Subgroup A) (x : A),
    p.Prime → 5 ≤ p → CatalogSimpleSections ↥X → Y ≤ X → ¬ X ≤ Y →
    Q ≤ X → IsPGroup p Q → ¬ p ∣ (Q.subgroupOf X).index → 3 ≤ Open.pRank p Q → Q ≤ Y →
    B ≤ Q → IsElemAbelian p B → Nat.card B = p ^ 2 → x ∈ B → x ≠ 1 →
    (∀ y ∈ centralizer (B : Set A), y ^ p = 1 → y ∈ B) →
    Open.pRank p (centralizer ({x} : Set A) ⊓ X) ≤ 2 →
    (∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) →
    (∀ E : Subgroup A, E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup A, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) →
    (∃ N : Subgroup A, N ≤ X ∧ (N.subgroupOf X).Normal ∧ (N.subgroupOf X).index = p) ∧
    (∀ W : Subgroup A, W ≤ X → B ≤ normalizer (W : Set A) →
      Nat.Coprime (Nat.card W) (2 * p) → W ≤ rankThreePrimeCore p X) ∧
    ∃ Q₀ : Subgroup A, Q₀ ≤ Q ∧ IsElemAbelian p Q₀ ∧ Nat.card Q₀ = p ^ p ∧
      ∀ a ∈ Q₀, a ≠ 1 → ∀ b ∈ Q₀, b ≠ 1 →
        ∃ g ∈ X ⊓ normalizer (Q₀ : Set A), g * a * g⁻¹ ∈ zpowers b

@[expose] def KFactP65RankTwoAt (A : Type) [Group A] [Finite A] : Prop :=
  ∀ (p : ℕ) (X Q B U : Subgroup A),
    p.Prime → 5 ≤ p → CatalogSimpleSections ↥X → Open.pRank p X = 2 →
    Q ≤ X → IsPGroup p Q → ¬ p ∣ (Q.subgroupOf X).index → IsCyclic (center Q) →
    B ≤ Q → IsElemAbelian p B → Nat.card B = p ^ 2 →
    U ≤ Q → IsElemAbelian p U → Nat.card U = p ^ 2 →
    (∀ g ∈ X, B.map (MulAut.conj g).toMonoidHom ≠ U) →
    (∀ w ∈ Q, orderOf w = p → (∀ q ∈ Q, q * w = w * q) →
      ∀ g ∈ X, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w) →
    (∃ Y : Subgroup A, Y ≤ X ∧ Y ≠ X ∧
      (∀ S : Subgroup A, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) ∧
      (∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y)) →
    ∀ W : Subgroup A, W ≤ X → B ⊔ U ≤ normalizer (W : Set A) →
      Nat.Coprime (Nat.card W) (2 * p) → W ≤ rankThreePrimeCore p X

@[expose] def KFactP65RankThreeS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.LocalAnalysis.RankThreeTheoremC.Setting G →
    KFactP65RankThreeAt G

@[expose] def KFactP65RankTwoS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.LocalAnalysis.RankThreeTheoremC.Setting G →
    KFactP65RankTwoAt G

theorem KFactP65RankThree.toS (h : KFactP65RankThree) : KFactP65RankThreeS :=
  fun G _ _ _ => h G

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
