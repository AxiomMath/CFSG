module

public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement

section Cyclic

variable {K : Type} [Group K]

theorem inv_apply_mem_of_apply_mem [Finite K] (X : Subgroup K) (a : MulAut K)
    (ha : ∀ x ∈ X, a x ∈ X) : ∀ x ∈ X, a⁻¹ x ∈ X := by
  have hle : X.map a.toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact ha x hx
  have heq : X.map a.toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective a.injective])
  intro x hx
  have : x ∈ X.map a.toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, rfl⟩ := this
  show a⁻¹ (a y) ∈ X
  simpa using hy

end Cyclic

end CFSG.GH74.GLS.IVK.Proofs2
