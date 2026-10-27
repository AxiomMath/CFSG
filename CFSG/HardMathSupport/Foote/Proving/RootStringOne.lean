module

public import CFSG.HardMathSupport.Foote.Proving.F4StringOne

public section

namespace CFSG.HardMathSupport.Foote.Proving

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.ClassicalInvolution.Balance.Bootstrap


theorem commutator_pinnedX_string_one {τ : Tag} {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) (hsum : IsRoot τ (α + β))
    (hno : ∀ p ∈ commCandidates, p ≠ (1, 1) → ¬ IsRoot τ (p.1 • α + p.2 • β)) :
    ∃ C : ℤ, (1 ≤ |C| ∧ |C| ≤ RootOps.commConstBound τ) ∧ ∀ (R : Type) [CommRing R] (c d : R),
      pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d) =
        pinnedX τ R (α + β) ((C : R) * c * d) := by
  obtain ⟨Cf, hCb, hF⟩ := exists_pinnedX_commFormula hα hβ hne hne'
  have hmem : ((1, 1) : ℕ × ℕ) ∈ commPairs τ α β := by
    rw [commPairs_eq_single_of_string_one hsum hno]
    simp
  refine ⟨Cf (1, 1), hCb (1, 1) hmem, ?_⟩
  intro R _ c d
  rw [hF R c d, commPairs_eq_single_of_string_one hsum hno]
  simp

end CFSG.HardMathSupport.Foote.Proving
