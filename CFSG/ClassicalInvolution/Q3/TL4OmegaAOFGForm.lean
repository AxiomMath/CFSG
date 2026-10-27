module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLComplex

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Gauss

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Module

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[instance_reducible, expose] noncomputable def gaussModule (a : V ≃ₗ[F] V)
    (ha : ∀ v, a (a v) = -v) : Module (GaussField F) V where
  smul z v := z.re • v + z.im • a v
  one_smul v := by
    show (1 : GaussField F).re • v + (1 : GaussField F).im • a v = v
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  mul_smul z w v := by
    show (z * w).re • v + (z * w).im • a v =
      z.re • (w.re • v + w.im • a v) + z.im • a (w.re • v + w.im • a v)
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_smul, ha]
    module
  smul_zero z := by
    show z.re • (0 : V) + z.im • a 0 = 0
    simp
  smul_add z u v := by
    show z.re • (u + v) + z.im • a (u + v) = (z.re • u + z.im • a u) + (z.re • v + z.im • a v)
    rw [map_add, smul_add, smul_add]
    abel
  add_smul z w v := by
    show (z + w).re • v + (z + w).im • a v = (z.re • v + z.im • a v) + (w.re • v + w.im • a v)
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, add_smul]
    abel
  zero_smul v := by
    show (0 : GaussField F).re • v + (0 : GaussField F).im • a v = 0
    simp

end Module

section Form

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (GaussField F) V] [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V}
  {a : V ≃ₗ[F] V}

theorem smul_eq (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (z : GaussField F) (v : V) : z • v = z.re • v + z.im • a v := by
  conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul z]
  rw [add_smul, smul_assoc, one_smul, smul_assoc, hω]

omit [IsScalarTower F (GaussField F) V] in
theorem a_a (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v) (v : V) :
    a (a v) = -v := by
  rw [← hω, ← hω, smul_smul]
  have h : (QuadraticAlgebra.omega : GaussField F) * QuadraticAlgebra.omega = -1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [h, neg_one_smul]

omit [Module (GaussField F) V] [IsScalarTower F (GaussField F) V] in
theorem polar_a_a (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (u v : V) :
    polar Q (a u) (a v) = -polar Q u v := by
  simp only [polar, ← map_add, hg]
  ring

omit [IsScalarTower F (GaussField F) V] in
theorem polar_a_right (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (u v : V) : polar Q u (a v) = polar Q (a u) v := by
  have h := polar_a_a hg (a u) v
  rw [a_a hω, polar_neg_left] at h
  linear_combination -h

variable (Q) in
@[expose] noncomputable def gaussBilin (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) : LinearMap.BilinForm (GaussField F) V :=
  LinearMap.mk₂ (GaussField F) (fun u v => (⟨polar Q u v, -polar Q (a u) v⟩ : GaussField F))
    (fun u₁ u₂ v => by
      ext
      · simp [polar_add_left]
      · simp [polar_add_left]
        ring)
    (fun z u v => by
      rw [smul_eq hω z u]
      ext
      · simp only [polar_add_left, polar_smul_left, smul_eq_mul, QuadraticAlgebra.re_mul]
        ring
      · simp only [polar_add_left, polar_smul_left, map_add, map_smul, a_a hω, polar_neg_left,
          smul_eq_mul, QuadraticAlgebra.im_mul]
        ring)
    (fun u v₁ v₂ => by
      ext
      · simp [polar_add_right]
      · simp [polar_add_right]
        ring)
    (fun z u v => by
      rw [smul_eq hω z v]
      ext
      · simp only [polar_add_right, polar_smul_right, polar_a_right hω hg, smul_eq_mul,
          QuadraticAlgebra.re_mul]
        ring
      · simp only [polar_add_right, polar_smul_right, polar_a_a hg, smul_eq_mul,
          QuadraticAlgebra.im_mul]
        ring)

theorem gaussBilin_apply (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (u v : V) :
    gaussBilin Q hω hg u v = (⟨polar Q u v, -polar Q (a u) v⟩ : GaussField F) := rfl

theorem gaussBilin_comm (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (u v : V) :
    gaussBilin Q hω hg u v = gaussBilin Q hω hg v u := by
  rw [gaussBilin_apply, gaussBilin_apply, polar_comm Q u v, polar_comm Q (a v) u,
    polar_a_right hω hg]

variable (Q) in
@[expose] noncomputable def gaussQuad (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) : QuadraticForm (GaussField F) V :=
  (gaussBilin Q hω hg).toQuadraticMap

theorem gaussQuad_apply (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (v : V) :
    gaussQuad Q hω hg v = gaussBilin Q hω hg v v := rfl

theorem polar_gaussQuad (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (u v : V) :
    polar (gaussQuad Q hω hg) u v = 2 * gaussBilin Q hω hg u v := by
  rw [gaussQuad, LinearMap.BilinMap.polar_toQuadraticMap, gaussBilin_comm hω hg v u]
  ring

theorem nondegenerate_gaussQuad (h2 : (2 : F) ≠ 0)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (hQ : (polarBilin Q).Nondegenerate) :
    (polarBilin (gaussQuad Q hω hg)).Nondegenerate := by
  refine ⟨fun u hu => hQ.1 u fun v => ?_, fun u hu => hQ.1 u fun v => ?_⟩
  · have h := hu v
    rw [polarBilin_apply_apply, polar_gaussQuad] at h
    have h' := congrArg QuadraticAlgebra.re h
    rw [polarBilin_apply_apply]
    simp only [QuadraticAlgebra.re_mul, gaussBilin_apply, QuadraticAlgebra.re_zero] at h'
    have h3 : (2 : GaussField F).re = 2 := rfl
    have h4 : (2 : GaussField F).im = 0 := rfl
    rw [h3, h4] at h'
    have h5 : (2 : F) * polar Q u v = 0 := by linear_combination h'
    exact (mul_eq_zero.mp h5).resolve_left h2
  · have h := hu v
    rw [polarBilin_apply_apply, polar_gaussQuad] at h
    have h' := congrArg QuadraticAlgebra.re h
    rw [polarBilin_apply_apply, polar_comm]
    simp only [QuadraticAlgebra.re_mul, gaussBilin_apply, QuadraticAlgebra.re_zero] at h'
    have h3 : (2 : GaussField F).re = 2 := rfl
    have h4 : (2 : GaussField F).im = 0 := rfl
    rw [h3, h4] at h'
    have h5 : (2 : F) * polar Q v u = 0 := by linear_combination h'
    exact (mul_eq_zero.mp h5).resolve_left h2

variable (F) in
@[expose] noncomputable def res : (V ≃ₗ[GaussField F] V) →* (V ≃ₗ[F] V) where
  toFun g := g.restrictScalars F
  map_one' := rfl
  map_mul' _ _ := rfl

theorem res_apply (g : V ≃ₗ[GaussField F] V) (v : V) : res F g v = g v := rfl

theorem res_injective : Function.Injective (res F (V := V)) := fun _ _ h =>
  LinearEquiv.ext fun v => LinearEquiv.congr_fun h v

theorem res_mul_a (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (g : V ≃ₗ[GaussField F] V) : res F g * a = a * res F g := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, res_apply, res_apply, ← hω, ← hω, map_smul]

theorem res_mem_orthogonalGroup (h2 : (2 : F) ≠ 0)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {g : V ≃ₗ[GaussField F] V}
    (hgq : g ∈ TauCeti.QuadraticMap.orthogonalGroup (gaussQuad Q hω hg)) :
    res F g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hgq ⊢
  intro v
  have h := congrArg QuadraticAlgebra.re (hgq v)
  rw [gaussQuad_apply, gaussQuad_apply, gaussBilin_apply, gaussBilin_apply] at h
  simp only at h
  rw [res_apply]
  rw [polar_self, polar_self] at h
  have h5 : (2 : F) * (Q (g v) - Q v) = 0 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
    linear_combination h
  have := (mul_eq_zero.mp h5).resolve_left h2
  linear_combination this

theorem exists_gauss_of_commute (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {ν : V ≃ₗ[F] V}
    (hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hc : ν * a = a * ν) :
    ∃ g : V ≃ₗ[GaussField F] V,
      g ∈ TauCeti.QuadraticMap.orthogonalGroup (gaussQuad Q hω hg) ∧ res F g = ν := by
  have hca : ∀ v, ν (a v) = a (ν v) := fun v => LinearEquiv.congr_fun hc v
  let g : V ≃ₗ[GaussField F] V :=
    { ν with
      map_smul' := fun z v => by
        show ν (z • v) = z • ν v
        rw [smul_eq hω, smul_eq hω, map_add, map_smul, map_smul, hca] }
  refine ⟨g, ?_, LinearEquiv.ext fun v => rfl⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  show gaussBilin Q hω hg (ν v) (ν v) = gaussBilin Q hω hg v v
  rw [gaussBilin_apply, gaussBilin_apply, ← hca, polar_map_of_mem hν, polar_map_of_mem hν]

end Form

end CFSG.ClassicalInvolution.Q3.TL4.Gauss
