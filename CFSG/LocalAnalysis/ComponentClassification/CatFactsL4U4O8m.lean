module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILc
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension)

variable {K : Type} [Field K]

theorem smul_decomp (c₀ : K) (z : extension c₀) (w : Fin 4 → extension c₀) :
    z • w = z.re • w + z.im • ((QuadraticAlgebra.omega : extension c₀) • w) := by
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [Algebra.smul_def, Algebra.smul_def]
  have hz : z = algebraMap K (extension c₀) z.re +
      algebraMap K (extension c₀) z.im * QuadraticAlgebra.omega := by
    ext <;> simp
  conv_lhs => rw [hz]
  ring

theorem exists_scalar_E (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ)
    (h2 : (2 : extension c₀) ≠ 0) (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))
    (X Y : GL (Fin (2 * 4)) K)
    (hχA : ∀ v, χ (Y.val *ᵥ v) = (QuadraticAlgebra.omega : extension c₀) • χ v)
    (hXY : X * Y = Y * X)
    (hcomm : ∀ U : Matrix (Fin 4) (Fin 4) (extension c₀),
      U = OIL.mU1 ∨ U = OIL.mUw (δ : extension c₀) ∨ U = OIL.mL1 →
        ∀ v, X.val *ᵥ χ.symm (U *ᵥ χ v) = χ.symm (U *ᵥ χ (X.val *ᵥ v))) :
    ∃ m : extension c₀, ∀ v, χ (X.val *ᵥ v) = m • χ v := by
  have hYs : ∀ w, χ.symm ((QuadraticAlgebra.omega : extension c₀) • w) = Y.val *ᵥ χ.symm w :=
    fun w => by
      apply χ.injective
      rw [LinearEquiv.apply_symm_apply, hχA, LinearEquiv.apply_symm_apply]
  have hXYv : ∀ v, X.val *ᵥ (Y.val *ᵥ v) = Y.val *ᵥ (X.val *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hXY]
  let f : (Fin 4 → extension c₀) →ₗ[extension c₀] (Fin 4 → extension c₀) :=
    { toFun := fun w => χ (X.val *ᵥ χ.symm w)
      map_add' := fun w w' => by rw [map_add, Matrix.mulVec_add, map_add]
      map_smul' := fun z w => by
        simp only [RingHom.id_apply]
        rw [smul_decomp c₀ z w, smul_decomp c₀ z (χ (X.val *ᵥ χ.symm w)), map_add, map_smul,
          map_smul, hYs, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXYv,
          map_add, map_smul, map_smul, hχA] }
  have hf : ∀ w, f w = χ (X.val *ᵥ χ.symm w) := fun w => rfl
  set M := LinearMap.toMatrix' f with hM
  have hMv : ∀ w, M *ᵥ w = f w := fun w => LinearMap.toMatrix'_mulVec f w
  have hMU : ∀ U : Matrix (Fin 4) (Fin 4) (extension c₀),
      U = OIL.mU1 ∨ U = OIL.mUw (δ : extension c₀) ∨ U = OIL.mL1 → M * U = U * M := by
    intro U hU
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMv, hMv, hf, hf]
    have h1 := hcomm U hU (χ.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [h1, LinearEquiv.apply_symm_apply]
  have hs := OIL.schur_matrix h2 (hMU _ (Or.inl rfl)) (hMU _ (Or.inr (Or.inl rfl)))
    (hMU _ (Or.inr (Or.inr rfl)))
  have hs' : ∀ w, M *ᵥ w = M 0 0 • w := fun w => by
    conv_lhs => rw [hs]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨M 0 0, fun v => ?_⟩
  have h1 := hMv (χ v)
  rw [hf, LinearEquiv.symm_apply_apply] at h1
  rw [← h1, hs']

theorem eq_re_add_im (c₀ : K) [Fact (¬ IsSquare c₀)]
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀)) (X Y : GL (Fin (2 * 4)) K)
    (hχA : ∀ v, χ (Y.val *ᵥ v) = (QuadraticAlgebra.omega : extension c₀) • χ v)
    (m : extension c₀) (hm : ∀ v, χ (X.val *ᵥ v) = m • χ v) (v : Fin (2 * 4) → K) :
    X.val *ᵥ v = m.re • v + m.im • (Y.val *ᵥ v) := by
  apply χ.injective
  rw [hm, map_add, map_smul, map_smul, hχA, smul_decomp]

theorem re_im_eq_zero {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : K) ≠ 0) (A : V →ₗ[K] V) (c₀ : K)
    (hAsim : ∀ v, Q (A v) = c₀ * Q v) (hadj : ∀ x y, polar Q (A x) y = polar Q x (A y))
    (hns : ∀ k : K, A ≠ k • LinearMap.id) (a b μ : K)
    (hsim : ∀ v, Q (a • v + b • A v) = μ * Q v) : a = 0 ∨ b = 0 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨ha, hb⟩ := h
  set κ := (μ - a ^ 2 - b ^ 2 * c₀) / (a * b) with hκ
  have h1 : ∀ v, polar Q v (A v) = κ * Q v := by
    intro v
    have e := hsim v
    rw [QuadraticMap.map_add Q (a • v) (b • A v), QuadraticMap.map_smul, QuadraticMap.map_smul,
      hAsim, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right] at e
    simp only [smul_eq_mul] at e
    rw [hκ]
    field_simp
    linear_combination e
  have h3 : ∀ v w, 2 * polar Q v (A w) = κ * polar Q v w := by
    intro v w
    have e := h1 (v + w)
    rw [A.map_add v w, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_add_right, h1 v, h1 w, QuadraticMap.map_add Q v w] at e
    have e2 : polar Q w (A v) = polar Q v (A w) := by rw [QuadraticMap.polar_comm, hadj]
    linear_combination e - e2
  apply hns (κ / 2)
  apply LinearMap.ext
  intro w
  have hw : A w - (κ / 2) • w = 0 := by
    apply hQ.1
    intro v
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_left,
      QuadraticMap.polar_smul_left, hadj, smul_eq_mul]
    have e := h3 w v
    have h2' : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    linear_combination (2⁻¹ : K) * e - polar Q w (A v) * h2'
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  exact sub_eq_zero.mp hw

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
