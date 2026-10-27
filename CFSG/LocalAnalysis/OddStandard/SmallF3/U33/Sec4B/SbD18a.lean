module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G]

@[expose] def Dsub (Ξ Y : Subgroup G) (hYc : ∀ y ∈ Y, ∀ x ∈ Ξ, x * y = y * x) (g : G) :
    Subgroup G where
  carrier := {x | x ∈ Ξ ∧ g * x * g⁻¹ * x⁻¹ ∈ Y}
  mul_mem' := by
    rintro a b ⟨haΞ, haY⟩ ⟨hbΞ, hbY⟩
    refine ⟨Ξ.mul_mem haΞ hbΞ, ?_⟩
    have h1 : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
        (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
    have h2 : a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ = g * b * g⁻¹ * b⁻¹ := by
      have h := hYc _ hbY a haΞ
      calc a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ = (g * b * g⁻¹ * b⁻¹) * a * a⁻¹ := by rw [h]
        _ = g * b * g⁻¹ * b⁻¹ := by group
    rw [h1, h2]
    exact Y.mul_mem haY hbY
  one_mem' := ⟨Ξ.one_mem, by simpa using Y.one_mem⟩
  inv_mem' := by
    rintro a ⟨haΞ, haY⟩
    refine ⟨Ξ.inv_mem haΞ, ?_⟩
    have h1 : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a := by group
    have h2 : a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a = (g * a * g⁻¹ * a⁻¹)⁻¹ := by
      have h := hYc _ (Y.inv_mem haY) a haΞ
      calc a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a
          = a⁻¹ * ((g * a * g⁻¹ * a⁻¹)⁻¹ * a) := by group
        _ = a⁻¹ * (a * (g * a * g⁻¹ * a⁻¹)⁻¹) := by rw [h]
        _ = (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
    show g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ ∈ Y
    rw [h1, h2]
    exact Y.inv_mem haY

theorem mem_Dsub {Ξ Y : Subgroup G} {hYc : ∀ y ∈ Y, ∀ x ∈ Ξ, x * y = y * x} {g x : G} :
    x ∈ Dsub Ξ Y hYc g ↔ x ∈ Ξ ∧ g * x * g⁻¹ * x⁻¹ ∈ Y := Iff.rfl

theorem Dsub_le {Ξ Y : Subgroup G} {hYc : ∀ y ∈ Y, ∀ x ∈ Ξ, x * y = y * x} {g : G} :
    Dsub Ξ Y hYc g ≤ Ξ := fun _ hx => hx.1

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
