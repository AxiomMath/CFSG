module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.LinearAlgebra

variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {W : Submodule K V} [FiniteDimensional K W]

@[expose] noncomputable def restrictEquiv {g : V ≃ₗ[K] V} (hgW : ∀ w ∈ W, g w ∈ W) :
    W ≃ₗ[K] W :=
  LinearEquiv.ofInjectiveEndo (g.toLinearMap.restrict hgW) (by
    intro x y hxy
    apply Subtype.ext
    have hval : g (x : V) = g (y : V) := by
      have := congrArg Subtype.val hxy
      simpa [LinearMap.restrict_apply] using this
    exact g.injective hval)

@[simp]
theorem restrictEquiv_apply {g : V ≃ₗ[K] V} (hgW : ∀ w ∈ W, g w ∈ W) (w : W) :
    (restrictEquiv hgW w : V) = g w := by
  change ((g.toLinearMap.restrict hgW) w : V) = g w
  rfl

theorem restrictEquiv_pow_apply' {g : V ≃ₗ[K] V} (hgW : ∀ w ∈ W, g w ∈ W)
    (n : ℕ) (w : W) : ((restrictEquiv hgW ^ n) w : V) = (g ^ n) w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, restrictEquiv_apply, ih, pow_succ',
        LinearEquiv.mul_apply]

theorem restrictEquiv_pow_eq_one {g : V ≃ₗ[K] V} (hgW : ∀ w ∈ W, g w ∈ W)
    {n : ℕ} (hg : g ^ n = 1) : restrictEquiv hgW ^ n = 1 := by
  ext w
  rw [restrictEquiv_pow_apply', hg]
  rfl

end CFSG.LinearAlgebra
