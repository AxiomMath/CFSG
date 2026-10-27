module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bProps

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def Harris82Lemma58bRowSL (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → pPrimeCore 2 X = ⊥ →
    ∀ p f : ℕ, p.Prime → p ≠ 2 →
    Blueprint.LieModel (X ⧸ center X) τ n p f → ∀ (k : ℕ) (c t : X)
    (Q L : Subgroup X), Lemma58bConfig X p k c t Q → IsTwoComponentIn L (centralizer {t}) →
      t ∈ L → IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) → IsCoverOf .POmegaOdd 3 p k 2 X

@[expose] def Harris82Lemma58bRowLie (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → pPrimeCore 2 X = ⊥ →
    ∀ p f : ℕ, p.Prime → p ≠ 2 →
    Blueprint.LieModel (X ⧸ center X) τ n p f → ∀ (k : ℕ) (c t : X)
    (Q L : Subgroup X), Lemma58bConfig X p k c t Q → IsTwoComponentIn L (centralizer {t}) →
      t ∈ L → (∃ (τ' : StatedLieTag) (n' : ℕ),
        Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) τ' n' p k) →
      ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsCoverOf .POmegaOdd m p k 2 X

theorem harris82Lemma58bRow_of_sl_of_lie {τ : StatedLieTag} {n : ℕ}
    (hSL : Harris82Lemma58bRowSL τ n) (hLie : Harris82Lemma58bRowLie τ n) :
    Harris82Lemma58bRow τ n :=
  fun X _ _ hX hO p f hp hp2 hm k c t Q L hcfg hL htL =>
    ⟨hLie X hX hO p f hp hp2 hm k c t Q L hcfg hL htL,
      hSL X hX hO p f hp hp2 hm k c t Q L hcfg hL htL⟩

end CFSG.ComponentClassification.HarrisLit.T1
