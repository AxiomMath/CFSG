module

public import CFSG.ClassicalInvolution.Asc77.AscSix66

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem l6_7_of_l6_6i (h : L6_6i p f) : L6_7 p f := by
  intro hp hq G _ _ Ω hΩ S R hR R' hR' hRS hR'S hne
  refine h hp hq G Ω hΩ (S : Subgroup G) S.isPGroup' {A | A ∈ RSet Ω ∧ A ≤ (S : Subgroup G)}
    (fun A hA => hA.2) ?_ (fun A hA => hA.1) R ⟨hR, hRS⟩ R' ⟨hR', hR'S⟩ hne
  intro A hA s hs
  refine ⟨RSet.conj hΩ.conjInvariant hA.1 s, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 : s⁻¹ * x * s ∈ (S : Subgroup G) := hA.2 hx
  have h2 : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs h1) (Subgroup.inv_mem _ hs)

theorem l6_7 (h62 : L6_2 p f) : L6_7 p f :=
  l6_7_of_l6_6i p f (l6_6i p f h62)

end CFSG.ClassicalInvolution.Asc77
