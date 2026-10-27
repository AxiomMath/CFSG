module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.LU.Local.Five

theorem perm_fin3_normal_gen : ∀ s τ : Equiv.Perm (Fin 3), s ≠ 1 → τ ^ 3 = 1 →
    τ = 1 ∨ τ = s ∨ τ = s * s ∨ ∃ g : Equiv.Perm (Fin 3), τ = s * (g * s * g⁻¹) := by decide

theorem perm_fin3_no_fixed : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → ∀ a, σ a ≠ a := by decide

theorem perm4_pow_three_or_four : ∀ g : Equiv.Perm (Fin 4), g ^ 3 = 1 ∨ g ^ 4 = 1 := by decide

section Transport

variable {T : Type} [Finite T]

theorem perm3_normal_gen (hT : Nat.card T = 3) (C : Subgroup (Equiv.Perm T)) [C.Normal]
    {s τ : Equiv.Perm T} (hs : s ∈ C) (hs1 : s ≠ 1) (hτ : τ ^ 3 = 1) : τ ∈ C := by
  have e : T ≃ Fin 3 := Finite.equivFinOfCardEq (by simpa using hT)
  let φ : Equiv.Perm T ≃* Equiv.Perm (Fin 3) := e.permCongrHom
  have hs1' : φ s ≠ 1 := fun h => hs1 (φ.injective (by rw [h, map_one]))
  have hτ' : φ τ ^ 3 = 1 := by rw [← map_pow, hτ, map_one]
  rcases perm_fin3_normal_gen (φ s) (φ τ) hs1' hτ' with h | h | h | ⟨g, h⟩
  · have : τ = 1 := φ.injective (by rw [h, map_one])
    rw [this]; exact C.one_mem
  · have : τ = s := φ.injective h
    rw [this]; exact hs
  · have : τ = s * s := φ.injective (by rw [h, map_mul])
    rw [this]; exact C.mul_mem hs hs
  · have : τ = s * (φ.symm g * s * (φ.symm g)⁻¹) := by
      apply φ.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h
    rw [this]
    exact C.mul_mem hs (Subgroup.Normal.conj_mem inferInstance s hs _)

theorem perm3_no_fixed (hT : Nat.card T = 3) {σ : Equiv.Perm T} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (a : T) : σ a ≠ a := by
  have e : T ≃ Fin 3 := Finite.equivFinOfCardEq (by simpa using hT)
  let φ : Equiv.Perm T ≃* Equiv.Perm (Fin 3) := e.permCongrHom
  have h1' : φ σ ≠ 1 := fun h => h1 (φ.injective (by rw [h, map_one]))
  have h3' : φ σ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  intro hfix
  have := perm_fin3_no_fixed (φ σ) h3' h1' (e a)
  apply this
  show e (σ (e.symm (e a))) = e a
  rw [Equiv.symm_apply_apply, hfix]

end Transport

end CFSG.GH74.GLS.LU.Local.Five
