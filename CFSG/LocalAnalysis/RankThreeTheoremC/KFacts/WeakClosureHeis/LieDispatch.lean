module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def SDLieDefAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p = ℓ → p ∣ Nat.card K → SylowDichotomyAt K p

@[expose] def SDLieCrossAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ ℓ → p ∣ Nat.card K → SylowDichotomyAt K p

@[expose] def SDPsp4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → LieModel K .PSp 2 p 1 →
    SylowDichotomyAt K p

@[expose] def SDG2p : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → LieModel K .G2 0 p 1 →
    SylowDichotomyAt K p

theorem sdLie_of_tags (hDef : ∀ t, SDLieDefAt t) (hCross : ∀ t, SDLieCrossAt t) : SDLie := by
  intro K _ _ hs hnab t n ℓ f hadm hmodel p hp h5 hpK
  by_cases hpℓ : p = ℓ
  · exact hDef t K hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  · exact hCross t K hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
