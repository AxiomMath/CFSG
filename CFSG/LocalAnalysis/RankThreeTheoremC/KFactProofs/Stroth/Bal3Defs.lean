module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

@[expose] def Input29_4Rank3 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    centralizer (L : Set Y) = ⊥ → CFSG.Open.pRank p (⊤ : Subgroup Y) = 3 →
    ∀ (z : Y) (D : Subgroup Y), IsElemAbelian p D → Nat.card D = p ^ 2 → z ∈ D → z ≠ 1 →
      CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set Y)) →
      (∃ g, IsPlaneDiagonal p D z g) →
      (∀ T : Subgroup Y, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set Y) → T = ⊥) ∨
        (∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set Y),
          zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom)

@[expose] def Bal3NoPermute : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.AGLEmbedding.CatalogSimpleSections H →
    ∀ (P : Sylow 3 H) (z : H) (D : Subgroup H), Lemma212Config 3 P z D → CentralizerEmbeds D z →
      ¬ CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint (G := H) 3 →
      CFSG.pCore 3 (H ⧸ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := H) 3) = ⊥ →
      ∀ K : Subgroup (H ⧸ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := H) 3),
        IsComponentOf K ⊤ →
          (P : Subgroup H).map (QuotientGroup.mk'
            (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := H) 3)) ≤
              normalizer (K : Set _)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
