module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Bridge
import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv

public section

namespace CFSG.ClassicalInvolution.Asc77

open scoped MatrixGroups

theorem oddCoreOf_map_eq_bot_of_sl2 {K G : Type} [Group K] [Group G] [Finite G] (ψ : K →* G)
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {R : Subgroup K}
    (e : R ≃* SL(2, F)) (hinv : ∃ y ∈ R.map ψ, orderOf y = 2) : oddCoreOf (R.map ψ) = ⊥ := by
  by_cases h3 : Nat.card F = 3
  · simp only [oddCoreOf,
      Q3.Q3T6.classicalInvolutionOddCore_map_eq_bot_of_card_three h3 ψ e hinv, Subgroup.map_bot]
  · have h2 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    exact ih8_oddCoreOf_map_eq_bot ψ ⟨k, hk⟩ (by omega) e hinv

end CFSG.ClassicalInvolution.Asc77
