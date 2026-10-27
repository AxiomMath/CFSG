module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def Lemma58bConfig (X : Type) [Group X] (p k : ℕ) (c t : X) (Q : Subgroup X) : Prop :=
  orderOf c = 2 ∧ c ∈ center X ∧ orderOf t = 2 ∧ t ∉ center X ∧
    IsTwoComponentIn Q (centralizer {t}) ∧ c ∈ Q ∧ 5 ≤ p ^ k ∧
    IsSLTwoOver (p ^ k) (↥Q ⧸ pPrimeCore 2 ↥Q)

@[expose] def Lemma58bConclusion (X : Type) [Group X] (p k : ℕ) (L : Subgroup X) : Prop :=
  ((∃ (τ : StatedLieTag) (n : ℕ), Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) τ n p k) →
      ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsCoverOf .POmegaOdd m p k 2 X) ∧
    (IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) → IsCoverOf .POmegaOdd 3 p k 2 X)

@[expose] def Harris82Lemma58bCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → pPrimeCore 2 X = ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsSimpleChevalleyOver p (X ⧸ center X) → ∀ (k : ℕ) (c t : X) (Q L : Subgroup X),
    Lemma58bConfig X p k c t Q → IsTwoComponentIn L (centralizer {t}) → t ∈ L →
      Lemma58bConclusion X p k L

@[expose] def Harris82Lemma58bNoConfig (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → pPrimeCore 2 X = ⊥ →
    ∀ p f : ℕ, p.Prime → p ≠ 2 →
    Blueprint.LieModel (X ⧸ center X) τ n p f → ∀ (k : ℕ) (c t : X) (Q : Subgroup X),
      ¬ Lemma58bConfig X p k c t Q

@[expose] def Harris82Lemma58bRow (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → pPrimeCore 2 X = ⊥ →
    ∀ p f : ℕ, p.Prime → p ≠ 2 →
    Blueprint.LieModel (X ⧸ center X) τ n p f → ∀ (k : ℕ) (c t : X)
    (Q L : Subgroup X), Lemma58bConfig X p k c t Q → IsTwoComponentIn L (centralizer {t}) →
      t ∈ L → Lemma58bConclusion X p k L

theorem harris82Lemma58bRow_of_noConfig {τ : StatedLieTag} {n : ℕ}
    (h : Harris82Lemma58bNoConfig τ n) : Harris82Lemma58bRow τ n :=
  fun X _ _ hX hO p f hp hp2 hm k c t Q _ hcfg _ _ =>
    (h X hX hO p f hp hp2 hm k c t Q hcfg).elim

theorem harris82Lemma58bCover_of_row (h : ∀ τ n, Harris82Lemma58bRow τ n) :
    Harris82Lemma58bCover := by
  intro X _ _ hX hO p hp hp2 hChev k c t Q L hcfg hL htL
  obtain ⟨τ, n, f, hm⟩ := hChev
  exact h τ n X hX hO p f hp hp2 hm k c t Q L hcfg hL htL

end CFSG.ComponentClassification.HarrisLit.T1
