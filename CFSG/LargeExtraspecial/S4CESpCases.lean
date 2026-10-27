module

public import CFSG.LargeExtraspecial.S4CESpMain
public import CFSG.LargeExtraspecial.S4CELinTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {K : Type*} [Group K] {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}
  {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem ker_eq_bot_of_naturalPair_lin (ha : a ≠ 0)
    (hpair : 2 ≤ finrank (ZMod 2) V ∧ X = ⊤ ∧ E₀ = centreGroup V a) (h : CEHyp π E a X E₀) :
    π.ker = ⊥ := by
  obtain ⟨hdim, rfl, rfl⟩ := hpair
  exact ker_eq_bot_of_linPair ha hdim h

theorem ker_eq_bot_of_naturalPair_sp
    (ha : a ≠ 0)
    (hpair : 4 ≤ finrank (ZMod 2) V ∧ ∃ (β : LinearMap.BilinForm (ZMod 2) V) (_ : β.IsAlt),
      β.Nondegenerate ∧ X = TauCeti.BilinForm.isometryGroup β ∧ E₀ = spPointRadical β a)
    (h : CEHyp π E a X E₀) : π.ker = ⊥ := by
  obtain ⟨hdim, β, hβ, hnd, rfl, rfl⟩ := hpair
  exact ker_eq_bot_of_spPair hβ hnd ha hdim h

end CFSG.LargeExtraspecial.S4
