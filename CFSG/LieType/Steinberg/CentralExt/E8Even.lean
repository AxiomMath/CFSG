module

public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier

public section

namespace CFSG.LieType.Steinberg.CentralExt

open CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e8_even_exists_section_of_central {E : Type} [Group E] [Finite E]
    (π : E →* adjointGroup .E8 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : adjointGroup .E8 K →* E, ∀ g, π (σ g) = g := by
  by_cases hK2 : Nat.card K = 2
  · exact FieldTwo.e8_two_exists_section hK2 E π hπ hcen
  by_cases hK4 : Nat.card K = 2 ^ 2
  · exact FieldFour.e8_four_exists_section hK4 E π hπ hcen
  have : Fintype K := Fintype.ofFinite K
  have hEven : Nat.card K % 2 = 0 := by
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have hPos : 1 < Nat.card K := Finite.one_lt_card
  have hK4' : Nat.card K ≠ 4 := by simpa only [show 2 ^ 2 = 4 by norm_num] using hK4
  have hK5 : 5 ≤ Nat.card K := by omega
  exact AdjointClosed.e8_exists_section_of_central hK5 hπ hcen

theorem e8_even_ker_eq_bot_of_perfect {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* adjointGroup .E8 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  obtain ⟨σ, hσ⟩ := e8_even_exists_section_of_central π hπ hcen
  exact SL2Closed.ker_eq_bot_of_section π hcen σ hσ

theorem e8_even_bijective_of_perfect {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* adjointGroup .E8 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : Function.Bijective π :=
  ⟨(MonoidHom.ker_eq_bot_iff π).mp (e8_even_ker_eq_bot_of_perfect π hπ hcen), hπ⟩

end CFSG.LieType.Steinberg.CentralExt
