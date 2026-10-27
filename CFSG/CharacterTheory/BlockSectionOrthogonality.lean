module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.Helpers
public import CFSG.CharacterTheory.BlockSectionOrthogonality.BlockAtoms
public import CFSG.CharacterTheory.BlockSectionOrthogonality.BlockOrthogonality

public section

open CFSG

namespace CFSG.BlockSectionOrthogonality

theorem block_section_orthogonality (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hpm : (p : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (B : Set (G → ℂ)) (hB : BlocksIsBlock m G B)
    (x y xp yp : G) (hx : BlocksIsPPart p x xp) (hy : BlocksIsPPart p y yp)
    (hxy : ¬ IsConj xp yp) :
    ∑ᶠ χ ∈ B, χ x * starRingEnd ℂ (χ y) = 0 := by
  exact Helpers.admissible_section_orthogonality p hp m hm hpm G B
    (Helpers.block_admissible m hm G hB) x y xp yp hx hy hxy

end CFSG.BlockSectionOrthogonality
