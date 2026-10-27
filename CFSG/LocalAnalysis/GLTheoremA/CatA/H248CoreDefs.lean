module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open

@[expose] def IsCorePrimeIndex (q : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ Q : TauCeti.PrimePower, Q.p = q ∧ Q.exponent = 1 ∧ (d = .A 2 Q ∨ d = .B 2 Q ∨ d = .G2 Q)

@[expose] def CoreRankFour : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d) → ∀ q : ℕ, q ≠ 2 → q = d.1.characteristic →
      ¬ CFSG.AGLEmbedding.IsRankOneLieIndex d.1 → ¬ IsCorePrimeIndex q d.1 →
        4 ≤ CFSG.Open.pRank q (⊤ : Subgroup K)

@[expose] def CorePrimeExcl : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (S ≃* CFSG.AGLEmbedding.CatGroup d) → IsCorePrimeIndex q d.1 →
        ∀ A : Subgroup (MulAut S), IsElemAbelian p A → Nat.card A < p ^ 3

@[expose] def CoreSmallVac : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → p ≠ 3 →
    ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
      Nonempty (S ≃* CFSG.AGLEmbedding.CatGroup d) →
      ((∃ Q : TauCeti.PrimePower, d.1 = .A 1 Q ∧ Q.card = 8) ∨
        (∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q ∧ (Q.card = 2 ∨ Q.card = 3)) ∨
        (∃ Q : TauCeti.PrimePower, d.1 = .B 3 Q ∧ Q.card = 3)) →
      ∀ A : Subgroup (MulAut S), IsElemAbelian p A → Nat.card A < p ^ 3

end CFSG.LocalAnalysis.GLTheoremA.H248
