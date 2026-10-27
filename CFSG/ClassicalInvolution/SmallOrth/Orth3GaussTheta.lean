module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussBasis

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap Matrix CFSG.ClassicalInvolution.Q3 CFSG.LieType.Universal.Unitary

section Orthonormal

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem polar_eq_dotProduct (b : Module.Basis ι F V)
    (horth : ∀ i j, polar Q (b i) (b j) = if i = j then 1 else 0) (x y : V) :
    polar Q x y = b.repr x ⬝ᵥ b.repr y := by
  have h1 : ∀ i, polar Q (b i) y = b.repr y i := by
    intro i
    rw [← polarBilin_apply_apply]
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [map_smul, polarBilin_apply_apply, horth, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  rw [← polarBilin_apply_apply]
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, h1, smul_eq_mul]
  rfl

theorem polar_map_eq_iff (b : Module.Basis ι F V)
    (horth : ∀ i j, polar Q (b i) (b j) = if i = j then 1 else 0) (φ : V →ₗ[F] V) :
    (∀ x y, polar Q (φ x) (φ y) = polar Q x y) ↔
      (LinearMap.toMatrix b b φ)ᵀ * LinearMap.toMatrix b b φ = 1 := by
  set M := LinearMap.toMatrix b b φ with hM
  constructor
  · intro h
    ext i j
    have h1 := h (b i) (b j)
    rw [polar_eq_dotProduct b horth, horth] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [hM, LinearMap.toMatrix_apply, dotProduct] using h1
  · intro h x y
    rw [polar_eq_dotProduct b horth (φ x) (φ y), polar_eq_dotProduct b horth x y,
      ← LinearMap.toMatrix_mulVec_repr b b φ x, ← LinearMap.toMatrix_mulVec_repr b b φ y,
      ← hM, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
      Matrix.one_mulVec]

end Orthonormal

section Theta

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {g : V ≃ₗ[F] V} {m : ℕ}

@[expose] noncomputable def thetaEnd (ab : AdaptedBasis Q g m) :
    Matrix (Fin m) (Fin m) (GaussField F) →* (V →ₗ[F] V) where
  toFun A := Matrix.toLin ab.basis ab.basis (gaussBlocks m A)
  map_one' := by
    rw [map_one, Matrix.toLin_one]
    rfl
  map_mul' A B := by
    rw [map_mul, Matrix.toLin_mul ab.basis ab.basis ab.basis]
    rfl

theorem thetaEnd_apply (ab : AdaptedBasis Q g m) (A : Matrix (Fin m) (Fin m) (GaussField F)) :
    thetaEnd ab A = Matrix.toLin ab.basis ab.basis (gaussBlocks m A) := rfl

theorem thetaEnd_injective (ab : AdaptedBasis Q g m) : Function.Injective (thetaEnd ab) :=
  fun _ _ h => gaussBlocks_injective ((Matrix.toLin ab.basis ab.basis).injective h)

theorem thetaEnd_scalar_omega (ab : AdaptedBasis Q g m) (hg2 : ∀ x, g (g x) = -x) :
    thetaEnd ab (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) =
      (g : V →ₗ[F] V) := by
  refine ab.basis.ext fun i => ?_
  rw [thetaEnd_apply, Matrix.toLin_self, gaussBlocks_scalar_omega]
  rcases i with k | k
  · rw [Fintype.sum_sum_type]
    simp [Matrix.one_apply, ab.inr_eq]
  · rw [Fintype.sum_sum_type]
    simp [Matrix.one_apply, ab.inr_eq, hg2]

@[expose] noncomputable def thetaHom (ab : AdaptedBasis Q g m) :
    GL (Fin m) (GaussField F) →* (V ≃ₗ[F] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp
    (Units.map (thetaEnd ab))

theorem thetaHom_apply (ab : AdaptedBasis Q g m) (A : GL (Fin m) (GaussField F)) (x : V) :
    thetaHom ab A x = thetaEnd ab (A : Matrix (Fin m) (Fin m) (GaussField F)) x := rfl

theorem thetaHom_injective (ab : AdaptedBasis Q g m) : Function.Injective (thetaHom ab) :=
  fun _ _ h => Units.ext (thetaEnd_injective ab (LinearMap.ext fun x => LinearEquiv.congr_fun h x))

section Unitary

variable [Finite F] [Fact (Nat.card F = 3)]

theorem polar_thetaEnd_iff (ab : AdaptedBasis Q g m) (A : Matrix (Fin m) (Fin m) (GaussField F)) :
    (∀ x y, polar Q (thetaEnd ab A x) (thetaEnd ab A y) = polar Q x y) ↔
      conjTr (gaussSigma (F := F)) A * A = 1 := by
  rw [polar_map_eq_iff ab.basis ab.orth, thetaEnd_apply, LinearMap.toMatrix_toLin,
    gaussBlocks_transpose gaussSigma gaussSigma_apply A, ← map_mul]
  constructor
  · intro h
    exact gaussBlocks_injective (h.trans (map_one _).symm)
  · intro h
    rw [h, map_one]

theorem thetaHom_mem_orthogonalGroup (ab : AdaptedBasis Q g m) (h2 : (2 : F) ≠ 0)
    {X : GL (Fin m) (GaussField F)}
    (hX : conjTr (gaussSigma (F := F)) (X : Matrix (Fin m) (Fin m) (GaussField F)) * X = 1) :
    thetaHom ab X ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  have h := (polar_thetaEnd_iff ab (X : Matrix (Fin m) (Fin m) (GaussField F))).mpr hX x x
  rw [polar_self_eq_two_mul, polar_self_eq_two_mul] at h
  exact mul_left_cancel₀ h2 h

theorem exists_unitary_of_commute (ab : AdaptedBasis Q g m) (hg2 : ∀ x, g (g x) = -x)
    {ν : V ≃ₗ[F] V} (hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hcomm : ν * g = g * ν) :
    ∃ A : Matrix (Fin m) (Fin m) (GaussField F), conjTr (gaussSigma (F := F)) A * A = 1 ∧
      (ν : V →ₗ[F] V) = thetaEnd ab A := by
  set M := LinearMap.toMatrix ab.basis ab.basis (ν : V →ₗ[F] V) with hM
  have hJ : LinearMap.toMatrix ab.basis ab.basis (g : V →ₗ[F] V) =
      Matrix.fromBlocks 0 (-1) 1 0 := by
    rw [← thetaEnd_scalar_omega ab hg2, thetaEnd_apply, LinearMap.toMatrix_toLin,
      gaussBlocks_scalar_omega]
  have hcomm' : (ν : V →ₗ[F] V) * (g : V →ₗ[F] V) = (g : V →ₗ[F] V) * (ν : V →ₗ[F] V) :=
    LinearMap.ext fun x => LinearEquiv.congr_fun hcomm x
  have hMJ : M * Matrix.fromBlocks 0 (-1) 1 0 = Matrix.fromBlocks 0 (-1) 1 0 * M := by
    rw [← hJ, hM, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, hcomm']
  obtain ⟨A, hA⟩ := exists_gaussBlocks_of_commute hMJ
  have hνA : (ν : V →ₗ[F] V) = thetaEnd ab A := by
    rw [thetaEnd_apply, hA, hM, Matrix.toLin_toMatrix]
  refine ⟨A, (polar_thetaEnd_iff ab A).mp ?_, hνA⟩
  intro x y
  rw [← hνA]
  exact polar_map_of_mem hν x y

end Unitary

end Theta

end CFSG.ClassicalGroups.Orthogonal.Small
