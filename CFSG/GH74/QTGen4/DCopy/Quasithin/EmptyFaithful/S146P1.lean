module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F7
public import CFSG.Quasithin.EmptyFaithful.S14612DA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def Stage14613LabP_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        (Case13One T M H p H₁ ∨ Case13Two T M H p H₁) ∨
          (Case13One T M H p H₂ ∨ Case13Two T M H p H₂)

theorem stage14613Lab_of_P_F4 (h : Stage14613LabP_F4) : Stage14613Lab_F4 := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t hdec
  exact h G T M S H PQ p hred H₀ H₁ H₂ t (hdec.toIsDecP hred)

end CFSG.Quasithin
