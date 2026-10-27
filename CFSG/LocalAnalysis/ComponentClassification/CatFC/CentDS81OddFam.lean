module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddPSL

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

@[expose] def OddDichotomyFamily (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t n p f →
    LieModel X t n p f → ∀ τ : X, orderOf τ = 2 → SolvableOrComponent X τ

theorem oddDichotomy_of_families (h : ∀ t, OddDichotomyFamily t) : OddDichotomy := by
  intro X _ _ _ _ hodd τ hτ
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  exact h t X n p f hp hp2 hadm hm τ hτ

theorem oddDichotomyFamily_twistedB2 : OddDichotomyFamily .twistedB2 := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddDichotomyFamily_twistedF4 : OddDichotomyFamily .twistedF4 := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddDichotomyFamily_Tits : OddDichotomyFamily .Tits := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddDichotomyFamily_PSL : OddDichotomyFamily .PSL := by
  intro X _ _ n p f hp hp2 hadm hm τ hτ
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  exact solvableOrComponent_of_matrixDichotomy
    (matrixDichotomy_statedSL hadm.2.2.1
      (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)) e τ hτ

end CFSG.ComponentClassification.CatFC.DS81
