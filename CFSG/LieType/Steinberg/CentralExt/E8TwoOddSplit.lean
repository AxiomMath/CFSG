module

public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

namespace CFSG.LieType.Steinberg.CentralExt.E8Two

open CFSG.Blueprint.Chevalley (adjointGroup)

theorem e8_exists_section_of_coprime {K : Type} [Field K] [Finite K] [CharP K 2]
    (E : Type) [Group E] [Finite E] (π : E →* adjointGroup .E8 K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : Nat.Coprime 2 (Nat.card π.ker)) :
    ∃ σ : adjointGroup .E8 K →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨O⟩, -, -⟩ := CFSG.LieType.Steinberg.Adjoint.e8_conclusionB K
  obtain ⟨C, -, hC'⟩ := CFSG.LieType.Steinberg.Adjoint.e8_commutatorFormula K O
  exact CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
    (CFSG.LieType.Steinberg.Adjoint.e8_isCTGroupDatum K)
    (CFSG.LieType.Steinberg.Adjoint.e8_steinbergExtras K)
    (CFSG.LieType.Steinberg.Adjoint.e8_chevalleyExtras K O C hC') E π hπ hcen hC

end CFSG.LieType.Steinberg.CentralExt.E8Two
