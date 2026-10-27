module

public import CFSG.LieType.SeitzGeneration.ThreeIndepOrth
public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow

public section

namespace CFSG.LieType.SeitzGeneration

theorem seitzOuter_dFour_three :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ p = 3 ∧ IsDFourIndex d.1 := by
  rintro d p - - - - E - - ⟨-, hscope, rfl, q, hq⟩
  exact absurd hscope.1 (not_rankLE2_orthogonal_three d (Or.inr (Or.inl ⟨4, q, hq⟩)))

theorem seitzXON_of_nonclassical
    (h : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ ¬ IsClassicalIndex d.1) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      (¬ IsClassicalIndex d.1 ∨ (p = 3 ∧ IsDFourIndex d.1)) :=
  SeitzPlanes.of_cover (S₁ := fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      ¬ IsClassicalIndex d.1)
    (S₂ := fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ p = 3 ∧ IsDFourIndex d.1)
    (fun _ _ _ _ _ hs => hs.2.2.imp (fun h3 => ⟨hs.1, hs.2.1, h3⟩)
      (fun h3 => ⟨hs.1, hs.2.1, h3⟩))
    h seitzOuter_dFour_three

end CFSG.LieType.SeitzGeneration
