module

public import CFSG.LargeExtraspecial.S10ModelB

public section

namespace CFSG.LargeExtraspecial.S10

theorem act_swap_transpose : ∀ (γ : Gm) (m : M2), act γ.swap m.transpose = (act γ m).transpose := by
  decide +kernel

theorem pf_transpose : ∀ m m' : M2, pf m.transpose m'.transpose = pf m m' := by decide +kernel

theorem qf_transpose : ∀ m : M2, qf m.transpose = qf m := by decide +kernel

theorem E00_transpose : E00.transpose = E00 := by decide +kernel

theorem τ₂_swap : τ₂.swap = τ₁ := by decide +kernel

theorem Γ₁_gen : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → s ≠ 1 → ∀ γ : Gm, γ.2 = 1 →
    ∃ i < 3, ∃ j < 2, γ = τ₁ ^ j * s ^ i := by
  decide +kernel

theorem Γ₂_gen : ∀ s : Gm, s.1 = 1 → s ^ 3 = 1 → s ≠ 1 → ∀ γ : Gm, γ.1 = 1 →
    ∃ i < 3, ∃ j < 2, γ = τ₂ ^ j * s ^ i := by
  decide +kernel

theorem τ₂_conj_mul : ∀ s : Gm, s.1 = 1 → s ^ 3 = 1 → s ≠ 1 →
    (τ₂ * (s * τ₂ * s⁻¹)) ^ 3 = 1 ∧ τ₂ * (s * τ₂ * s⁻¹) ≠ 1 ∧ (τ₂ * (s * τ₂ * s⁻¹)).1 = 1 := by
  decide +kernel

theorem exists_pf_sep_Γ₁ : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → s ≠ 1 →
    ∃ m : M2, pf E00 m = 0 ∧ pf (act s E00) m = 1 := by
  decide +kernel

@[expose, irreducible] def σ₁ : Gm := (⟨!![1, 1; 1, 0], by decide +kernel⟩, 1)

@[expose, irreducible] def σ₂ : Gm := (1, ⟨!![1, 1; 1, 0], by decide +kernel⟩)

theorem σ₁_spec : σ₁.2 = 1 ∧ σ₁ ^ 3 = 1 ∧ σ₁ ≠ 1 := by decide +kernel

theorem σ₂_spec : σ₂.1 = 1 ∧ σ₂ ^ 3 = 1 ∧ σ₂ ≠ 1 := by decide +kernel

theorem pow_four_pow_of_cube {X : Type*} [Monoid X] {s : X} (hs : s ^ 3 = 1) (k : ℕ) :
    s ^ (4 ^ k) = s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, show 4 = 3 + 1 by rfl, pow_succ, hs, one_mul]

end CFSG.LargeExtraspecial.S10
