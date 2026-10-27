module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S14612DC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def NoE9Z4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → ¬ IsE9Z4Shape T H p

@[expose] def Stage14612PartP_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      (p = 3 ∨ p = 5) ∧ ∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDecP T M H p H₀ H₁ H₂ t

theorem stage14612PartP_of_class_F4 (hc : Stage14612Class) (hN : NoE9Z4_F4) : Stage14612PartP_F4 := by
  intro G _ _ T M S H PQ p hred hmax
  refine ⟨S.p_eq_three_or_five_of_isRedCE hred, ?_⟩
  rcases hc G T M S H PQ p hred with hdec | hshape
  · exact hdec
  · exact absurd hshape (hN G T M S H PQ p hred hmax)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M : Subgroup G}

end CFSG.Quasithin
