module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

@[expose] def KFactKlingenFiveLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (d : TauCeti.ValidLieTypeIndex), IsKlingenIndex p d →
    ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow p Y) (B Y₀ : Subgroup Y),
      B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 → GLBWeakCore p (T : Subgroup Y) ≤ Y₀ →
      Y₀ ≠ ⊤ →
      Y₀ ≤ Subgroup.normalizer (B : Set Y) ∧ Nat.card (T : Subgroup Y) = p ^ 4 ∧
        Nat.card (centerOf (T : Subgroup Y)) = p

@[expose] def KFactBlockHeisenbergInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    pCoreOf 2 M ≤ S → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ R₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      R₁ ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      R₁ ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ →
      Nat.card R₁ = p ^ 4 →
      (∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ R₁ ∧ Nat.card E = p ^ 3 ∧
        (∀ x ∈ E, x ^ p = 1) ∧ ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a) →
      (∀ v ∈ barM M L, (∃ r ∈ R₁, r * v⁻¹ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
        v ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L)) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
