module

public import CFSG.CGT.T75I.HatData

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem perfect_of_hat {Y : Type} [Group Y] (h : IsHatA 6 Y ∨ IsHatA 7 Y) : commutator Y = ⊤ := by
  rcases h with h | h
  · exact (IsHatA.exists_data h).1
  · exact (IsHatA.exists_data h).1

end CFSG.CGT.T75I
