module

public import CFSG.LieType.Chevalley.RootCommutator

public section

namespace CFSG.HardMathSupport.Foote.Proving

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps

open scoped commutatorElement


theorem commute_pinnedX_of_commPairs_eq_nil {τ : Tag} {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) (hnil : commPairs τ α β = [])
    (R : Type) [CommRing R] (c d : R) :
    Commute (pinnedX τ R α c) (pinnedX τ R β d) := by
  obtain ⟨_, _, hF⟩ := exists_pinnedX_commFormula hα hβ hne hne'
  have h := hF R c d
  rw [hnil, List.map_nil, List.prod_nil] at h
  have hc : ⁅pinnedX τ R α c, pinnedX τ R β d⁆ = 1 := by
    rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
    exact h
  exact commutatorElement_eq_one_iff_mul_comm.mp hc

end CFSG.HardMathSupport.Foote.Proving
