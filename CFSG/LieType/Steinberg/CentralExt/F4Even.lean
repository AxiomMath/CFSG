module

public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier

public section

namespace CFSG.LieType.Steinberg.CentralExt

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem f4_even_exists_section_of_central {E : Type} [Group E] [Finite E]
    (hK4 : 4 ≤ Nat.card K) (π : E →* adjointGroup .F4 K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : adjointGroup .F4 K →* E, ∀ g, π (σ g) = g := by
  by_cases hK4eq : Nat.card K = 4
  · exact FieldFour.f4_four_exists_section hK4eq E π hπ hcen
  · have hK5 : 5 ≤ Nat.card K := by omega
    exact AdjointClosed.f4_exists_section_of_central hK5 hπ hcen

theorem f4_even_ker_eq_bot_of_perfect {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (hK4 : 4 ≤ Nat.card K) (π : E →* adjointGroup .F4 K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  obtain ⟨σ, hσ⟩ := f4_even_exists_section_of_central hK4 π hπ hcen
  exact SL2Closed.ker_eq_bot_of_section π hcen σ hσ

theorem f4_even_bijective_of_perfect {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (hK4 : 4 ≤ Nat.card K) (π : E →* adjointGroup .F4 K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    Function.Bijective π :=
  ⟨(MonoidHom.ker_eq_bot_iff π).mp (f4_even_ker_eq_bot_of_perfect hK4 π hπ hcen), hπ⟩

end CFSG.LieType.Steinberg.CentralExt
