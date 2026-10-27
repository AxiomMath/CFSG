module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

structure AutModel (P : Type*) [Group P] (n : ℕ) where
  π : P →* Equiv.Perm (Fin n)
  inj : Function.Injective π
  cent : ∀ c : Equiv.Perm (Fin n), (∀ g, c * π g = π g * c) → c = 1
  ext : ∀ α : MulAut P, ∃ τ : Equiv.Perm (Fin n), ∀ g, τ * π g * τ⁻¹ = π (α g)

namespace AutModel

variable {P : Type*} [Group P] {n : ℕ} (M : AutModel P n)

noncomputable def τ (α : MulAut P) : Equiv.Perm (Fin n) := (M.ext α).choose

theorem τ_spec (α : MulAut P) (g : P) : M.τ α * M.π g * (M.τ α)⁻¹ = M.π (α g) :=
  (M.ext α).choose_spec g

theorem eq_τ {α : MulAut P} {σ : Equiv.Perm (Fin n)} (h : ∀ g, σ * M.π g * σ⁻¹ = M.π (α g)) :
    σ = M.τ α := by
  have h1 : (M.τ α)⁻¹ * σ = 1 := M.cent _ fun g => by
    calc (M.τ α)⁻¹ * σ * M.π g = (M.τ α)⁻¹ * (σ * M.π g * σ⁻¹) * σ := by group
      _ = (M.τ α)⁻¹ * (M.τ α * M.π g * (M.τ α)⁻¹) * σ := by rw [h g, M.τ_spec]
      _ = M.π g * ((M.τ α)⁻¹ * σ) := by group
  calc σ = M.τ α * ((M.τ α)⁻¹ * σ) := by group
    _ = M.τ α := by rw [h1, mul_one]

noncomputable def T : MulAut P →* Equiv.Perm (Fin n) where
  toFun := M.τ
  map_one' := (M.eq_τ fun g => by rw [one_mul, inv_one, mul_one, MulAut.one_apply]).symm
  map_mul' α β := (M.eq_τ (α := α * β) (σ := M.τ α * M.τ β) fun g => by
    calc M.τ α * M.τ β * M.π g * (M.τ α * M.τ β)⁻¹ =
        M.τ α * (M.τ β * M.π g * (M.τ β)⁻¹) * (M.τ α)⁻¹ := by group
      _ = M.π ((α * β) g) := by rw [M.τ_spec, M.τ_spec, MulAut.mul_apply]).symm

theorem T_spec (α : MulAut P) (g : P) : M.T α * M.π g * (M.T α)⁻¹ = M.π (α g) :=
  M.τ_spec α g

theorem eq_T {α : MulAut P} {σ : Equiv.Perm (Fin n)} (h : ∀ g, σ * M.π g * σ⁻¹ = M.π (α g)) :
    σ = M.T α :=
  M.eq_τ h

theorem T_conj (h : P) : M.T (MulAut.conj h) = M.π h :=
  (M.eq_T fun g => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]).symm

theorem T_injective : Function.Injective M.T := by
  rw [injective_iff_map_eq_one]
  intro α hα
  ext g
  apply M.inj
  have h := M.T_spec α g
  rw [hα, one_mul, inv_one, mul_one] at h
  rw [MulAut.one_apply, ← h]

theorem orderOf_T (α : MulAut P) : orderOf (M.T α) = orderOf α :=
  orderOf_injective M.T M.T_injective α

theorem fixed_iff (α : MulAut P) (g : P) : α g = g ↔ M.T α * M.π g = M.π g * M.T α := by
  rw [← M.inj.eq_iff, ← M.T_spec α g]
  constructor
  · intro h
    calc M.T α * M.π g = M.T α * M.π g * (M.T α)⁻¹ * M.T α := by group
      _ = M.π g * M.T α := by rw [h]
  · intro h
    rw [h, mul_inv_cancel_right]

end AutModel

end CFSG.ComponentClassification.HarrisLit.P1
