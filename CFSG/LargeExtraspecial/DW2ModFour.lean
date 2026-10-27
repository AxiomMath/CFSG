module

public import CFSG.LargeExtraspecial.Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsA2Class (f : LinearMap.BilinForm (ZMod 2) V) (X : Subgroup (V ≃ₗ[ZMod 2] V))
    (D : Set (V ≃ₗ[ZMod 2] V)) : Prop :=
  X = Subgroup.closure D ∧ (∃ d₀ ∈ D, ∀ d, d ∈ D ↔ ∃ g ∈ X, d = g * d₀ * g⁻¹) ∧
    ∀ d ∈ D, IsSpTypeA f d 2

@[expose] def HasFourGroup (D : Set (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ a * b = b * a ∧ a * b ∈ D

theorem IsA2Class.exists_conj {f : LinearMap.BilinForm (ZMod 2) V}
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} {D : Set (V ≃ₗ[ZMod 2] V)} (h : IsA2Class f X D)
    {d d' : V ≃ₗ[ZMod 2] V} (hd : d ∈ D) (hd' : d' ∈ D) : ∃ g ∈ X, d' = g * d * g⁻¹ := by
  obtain ⟨d₀, -, hD⟩ := h.2.1
  obtain ⟨g, hg, rfl⟩ := (hD d).mp hd
  obtain ⟨g', hg', rfl⟩ := (hD d').mp hd'
  exact ⟨g' * g⁻¹, X.mul_mem hg' (X.inv_mem hg), by group⟩

variable [FiniteDimensional (ZMod 2) V] {f : LinearMap.BilinForm (ZMod 2) V}

end CFSG.LargeExtraspecial.DW
