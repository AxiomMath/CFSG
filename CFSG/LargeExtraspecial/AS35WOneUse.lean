module

public import CFSG.LargeExtraspecial.AS35WOne

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

@[expose] def OneClass (X : Type) [Group X] : Prop :=
  ∀ x y : X, orderOf x = 2 → orderOf y = 2 → IsConj x y

variable {X Y : Type} [Group X] [Group Y]

theorem w2Good_of_oneClass [Finite X] (h : OneClass X) (hr : 3 ≤ Open.twoRank X) : W2Good X :=
  fun z hz => (hz.false_of_oneClass (fun x hx => h z x hz.orderOf_eq hx) hr).elim

theorem OneClass.of_mulEquiv (e : X ≃* Y) (h : OneClass Y) : OneClass X := by
  intro x y hx hy
  rw [← isConj_map_iff e]
  exact h _ _ (by rw [MulEquiv.orderOf_eq]; exact hx) (by rw [MulEquiv.orderOf_eq]; exact hy)

end AS35W

end CFSG.LargeExtraspecial
