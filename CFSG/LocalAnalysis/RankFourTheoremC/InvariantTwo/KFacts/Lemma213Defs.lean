module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def LinesTransitive {X : Type*} [Group X] (D : Subgroup X) : Prop :=
  ∀ x ∈ D, x ≠ 1 → ∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set X),
    zpowers y = (zpowers x).map (MulAut.conj h).toMonoidHom

@[expose] def InvolvedInSymm (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∃ (V : Subgroup (Equiv.Perm (Fin p))) (f : V →* S), Function.Surjective f

@[expose] def GL83I294Two : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    centralizer (L : Set X) = ⊥ → ∀ (D : Subgroup X), IsElemAbelian p D → Nat.card D = p ^ 2 →
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X)) →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ z g : X, z ∈ D → z ≠ 1 →
      IsPlaneDiagonal p D z g →
      (∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
      (∀ T : Subgroup X, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set X) → T = ⊥) ∨
        LinesTransitive D

@[expose] def GL83I203Sigma : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    (∃ a b : S, a * b ≠ b * a) → IsCatalogGroup S → p ∣ Nat.card S → InvolvedInSymm p S →
    ∀ x : S, orderOf x = p → ∀ A : Subgroup (MulAut S), p.Coprime (Nat.card A) →
      MulAut.conj x ∈ normalizer (A : Set (MulAut S)) → A = ⊥

@[expose] def SigmaCentralizerPGroup : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    (∃ a b : S, a * b ≠ b * a) → IsCatalogGroup S → p ∣ Nat.card S → InvolvedInSymm p S →
    ∀ x : S, orderOf x = p → ∀ φ : MulAut S, p.Coprime (orderOf φ) → φ x = x → φ = 1

end CFSG.LocalAnalysis.RankFourTheoremC
