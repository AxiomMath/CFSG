module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {Γ : Type*} [Group Γ] (B : Subgroup Γ)

@[expose] def fgCj (f : Γ) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) : MulAut ↥B where
  toFun g := ⟨f * g * f⁻¹, (hf g).1 g.2⟩
  invFun g := ⟨f⁻¹ * g * f, by
    have h := (hf (f⁻¹ * g * f)).2
    have h2 : f * (f⁻¹ * (g : Γ) * f) * f⁻¹ = g := by group
    rw [h2] at h
    exact h g.2⟩
  left_inv g := by
    apply Subtype.ext
    show f⁻¹ * (f * (g : Γ) * f⁻¹) * f = g
    group
  right_inv g := by
    apply Subtype.ext
    show f * (f⁻¹ * (g : Γ) * f) * f⁻¹ = g
    group
  map_mul' a b := by
    apply Subtype.ext
    show f * ((a : Γ) * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹)
    group

theorem coe_fgCj (f : Γ) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) (g : ↥B) :
    ((fgCj B f hf g : ↥B) : Γ) = f * g * f⁻¹ :=
  rfl

theorem coe_fgCj_pow (f : Γ) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) (n : ℕ) (g : ↥B) :
    (((fgCj B f hf ^ n) g : ↥B) : Γ) = f ^ n * g * (f ^ n)⁻¹ := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, coe_fgCj, pow_succ]
    group

theorem fgCj_pow_eq_one (f : Γ) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) {n : ℕ} (hn : f ^ n = 1) :
    fgCj B f hf ^ n = 1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [coe_fgCj_pow, hn]
  simp

@[expose] def fgPerm (R : Type*) : MulAut ↥B →* Equiv.Perm (↥B → R) where
  toFun c :=
    { toFun := fun χ g => χ (c.symm g)
      invFun := fun χ g => χ (c g)
      left_inv := fun χ => by
        funext g
        simp
      right_inv := fun χ => by
        funext g
        simp }
  map_one' := by
    ext χ g
    rfl
  map_mul' a b := by
    ext χ g
    rfl

theorem fgPerm_apply (R : Type*) (c : MulAut ↥B) (χ : ↥B → R) (g : ↥B) :
    fgPerm B R c χ g = χ (c.symm g) :=
  rfl

theorem fgPerm_pow_five (R : Type*) (f : Γ) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B)
    (hf5 : f ^ 5 = 1) : fgPerm B R (fgCj B f hf) ^ 5 = 1 := by
  rw [← map_pow, fgCj_pow_eq_one B f hf hf5, map_one]

end CFSG.OddStandard.SmallF3.Omega
