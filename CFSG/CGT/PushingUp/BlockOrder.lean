module

public import CFSG.CGT.PushingUp.Defs

public section

namespace CFSG.CGT.PushingUp

open CFSG CFSG.RankThree.PartOne
open scoped Pointwise

variable {G : Type} [Group G]

theorem arrow_le {X Y : Subgroup G} (h : Arrow X Y) : X ≤ Y := by
  rcases h with rfl | ⟨_, _, _, _, _, _, _, hXY, _⟩
  · exact le_rfl
  · exact hXY

theorem arrow_refl (X : Subgroup G) : Arrow X X := Or.inl rfl

theorem exists_maximal_inOmega [Finite G] {X : Subgroup G} (hX : InOmega X) :
    ∃ X' : Subgroup G, InOmega X' ∧ ∀ Y : Subgroup G, InOmega Y → Arrow X' Y → Y = X' := by
  obtain ⟨X', hX', hmax⟩ := Set.exists_max_image {Y : Subgroup G | InOmega Y}
    (fun Y => Nat.card Y) (Set.toFinite _) ⟨X, hX⟩
  refine ⟨X', hX', fun Y hY hXY => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge (arrow_le hXY) (hmax Y hY)).symm

end CFSG.CGT.PushingUp
