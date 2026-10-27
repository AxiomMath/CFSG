module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

open Matrix

namespace CFSG.LinearAlgebra

theorem specialLinear_irreducible_map_conj {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] {W : Subgroup (Matrix.SpecialLinearGroup n K)}
    (hirr : ∀ Z : Submodule K (n → K),
      (∀ s ∈ W, ∀ v ∈ Z, (s : Matrix n n K) *ᵥ v ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (g : Matrix.SpecialLinearGroup n K) :
    ∀ X : Submodule K (n → K),
      (∀ s ∈ W.map (MulAut.conj g).toMonoidHom, ∀ v ∈ X,
        (s : Matrix n n K) *ᵥ v ∈ X) → X = ⊥ ∨ X = ⊤ := by
  intro X hX
  let φ : (n → K) ≃ₗ[K] (n → K) := Matrix.SpecialLinearGroup.toLin' g
  have hXlin : ∀ s ∈ W.map (MulAut.conj g).toMonoidHom, ∀ v ∈ X,
      Matrix.SpecialLinearGroup.toLin' s v ∈ X := by
    intro s hs v hv
    simpa only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using hX s hs v hv
  have hconj : ∀ s : Matrix.SpecialLinearGroup n K,
      Matrix.SpecialLinearGroup.toLin' ((MulAut.conj g) s) * φ =
        φ * Matrix.SpecialLinearGroup.toLin' s := by
    intro s
    calc Matrix.SpecialLinearGroup.toLin' ((MulAut.conj g) s) * φ
        = Matrix.SpecialLinearGroup.toLin' ((MulAut.conj g) s * g) :=
          (map_mul Matrix.SpecialLinearGroup.toLin' _ _).symm
      _ = Matrix.SpecialLinearGroup.toLin' (g * s) := by
          rw [MulAut.conj_apply]
          congr 1
          group
      _ = φ * Matrix.SpecialLinearGroup.toLin' s := map_mul Matrix.SpecialLinearGroup.toLin' _ _
  have hZinv : ∀ s ∈ W, ∀ z ∈ X.comap (φ : (n → K) →ₗ[K] (n → K)),
      Matrix.SpecialLinearGroup.toLin' s z ∈ X.comap (φ : (n → K) →ₗ[K] (n → K)) := by
    intro s hs z hz
    rw [Submodule.mem_comap] at hz ⊢
    have hs' : (MulAut.conj g) s ∈ W.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hs
    have h := hXlin _ hs' (φ z) hz
    have h2 : Matrix.SpecialLinearGroup.toLin' ((MulAut.conj g) s) (φ z) =
        φ (Matrix.SpecialLinearGroup.toLin' s z) := by
      change (Matrix.SpecialLinearGroup.toLin' ((MulAut.conj g) s) * φ) z =
        (φ * Matrix.SpecialLinearGroup.toLin' s) z
      rw [hconj]
    rw [h2] at h
    exact h
  have hZmat : ∀ s ∈ W, ∀ v ∈ X.comap (φ : (n → K) →ₗ[K] (n → K)),
      (s : Matrix n n K) *ᵥ v ∈ X.comap (φ : (n → K) →ₗ[K] (n → K)) := by
    intro s hs v hv
    simpa only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using hZinv s hs v hv
  rcases hirr _ hZmat with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective φ.surjective X, h, Submodule.map_bot]
  · right
    rw [← Submodule.map_comap_eq_of_surjective φ.surjective X, h, Submodule.map_top]
    exact LinearMap.range_eq_top_of_surjective φ.toLinearMap φ.surjective

end CFSG.LinearAlgebra
