module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.W

@[expose] def V4m (p : Fin 5) (σ : Equiv.Perm (Fin 5)) : Prop :=
  σ p = p ∧ (σ = 1 ∨ ∀ x, x ≠ p → σ x ≠ x ∧ σ (σ x) = x)

instance (p : Fin 5) : DecidablePred (V4m p) := fun σ => by unfold V4m; infer_instance

theorem V4m_mul : ∀ (p : Fin 5) (σ τ : Equiv.Perm (Fin 5)), V4m p σ → V4m p τ → V4m p (σ * τ) := by
  decide +kernel

theorem V4m_sq : ∀ (p : Fin 5) (σ : Equiv.Perm (Fin 5)), V4m p σ → σ * σ = 1 := by
  decide +kernel

theorem V4m_one (p : Fin 5) : V4m p 1 := ⟨rfl, Or.inl rfl⟩

theorem V4m_five : ∀ p q : Fin 5, p ≠ q → ∃ σ τ : Equiv.Perm (Fin 5), V4m p σ ∧ V4m q τ ∧
    ∀ x, ((σ * τ) ^ 24) x ≠ x := by
  decide +kernel

theorem S4_commutator : ∀ c : Equiv.Perm (Fin 4), c ^ 3 = 1 → c ≠ 1 →
    ∃ g : Equiv.Perm (Fin 4), (c * (g * c⁻¹ * g⁻¹)) ^ 2 = 1 ∧ c * (g * c⁻¹ * g⁻¹) ≠ 1 := by
  decide +kernel

theorem exists_three_cycle : ∃ c : Equiv.Perm (Fin 4), c ^ 3 = 1 ∧ c ≠ 1 := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_, ?_⟩ <;> decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.W
