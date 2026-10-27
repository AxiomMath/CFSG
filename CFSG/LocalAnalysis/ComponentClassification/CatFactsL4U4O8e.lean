module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsQuadratic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Module QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare (orthogonalOperatorCentralizer)
open CFSG.GroupTheory.WeirSylow (IsPlusType)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def evalE (A : V ≃ₗ[K] V) (c₀ : K) (hsq : ∀ x, A (A x) = c₀ • x) :
    extension c₀ →+* Module.End K V where
  toFun z := z.re • (1 : Module.End K V) + z.im • A.toLinearMap
  map_one' := by ext x; simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    apply LinearMap.ext
    intro x
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearEquiv.coe_toLinearMap, Module.End.mul_apply,
      map_add, map_smul, hsq]
    module
  map_zero' := by ext x; simp
  map_add' z w := by
    apply LinearMap.ext
    intro x
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearEquiv.coe_toLinearMap]
    module

@[expose, instance_reducible] def modE (A : V ≃ₗ[K] V) (c₀ : K) (hsq : ∀ x, A (A x) = c₀ • x) :
    Module (extension c₀) V :=
  Module.compHom V (evalE A c₀ hsq)

variable (A : V ≃ₗ[K] V) (c₀ : K) (hsq : ∀ x, A (A x) = c₀ • x)

theorem smul_def (z : extension c₀) (x : V) :
    letI := modE A c₀ hsq
    z • x = z.re • x + z.im • A x := rfl

theorem omega_smul (x : V) :
    letI := modE A c₀ hsq
    (QuadraticAlgebra.omega : extension c₀) • x = A x := by
  rw [smul_def]
  simp

theorem isScalarTower :
    letI := modE A c₀ hsq
    IsScalarTower K (extension c₀) V := by
  let := modE A c₀ hsq
  refine ⟨fun a z x => ?_⟩
  rw [smul_def, smul_def]
  simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul, mul_smul,
    smul_add]

theorem span_omega (z : extension c₀) :
    ∃ a b : K, z = algebraMap K (extension c₀) a +
      algebraMap K (extension c₀) b * QuadraticAlgebra.omega :=
  ⟨z.re, z.im, by ext <;> simp⟩

@[expose] def toE (g : V ≃ₗ[K] V) (hg : ∀ x, g (A x) = A (g x)) :
    letI := modE A c₀ hsq
    V ≃ₗ[extension c₀] V :=
  letI := modE A c₀ hsq
  { toFun := g
    invFun := g.symm
    map_add' := g.map_add
    map_smul' := fun z x => by
      change g (z • x) = z • g x
      rw [smul_def, smul_def, map_add, map_smul, map_smul, hg]
    left_inv := g.left_inv
    right_inv := g.right_inv }

@[expose] def ofE :
    letI := modE A c₀ hsq
    (V ≃ₗ[extension c₀] V) → (V ≃ₗ[K] V) := by
  letI := modE A c₀ hsq
  letI := isScalarTower A c₀ hsq
  exact fun g => g.restrictScalars K

theorem ofE_apply :
    letI := modE A c₀ hsq
    ∀ (g : V ≃ₗ[extension c₀] V) (x : V), ofE A c₀ hsq g x = g x := by
  intros
  rfl

theorem ofE_comm :
    letI := modE A c₀ hsq
    ∀ (g : V ≃ₗ[extension c₀] V) (x : V), ofE A c₀ hsq g (A x) = A (ofE A c₀ hsq g x) := by
  let := modE A c₀ hsq
  intro g x
  rw [ofE_apply, ofE_apply, ← omega_smul A c₀ hsq, map_smul, omega_smul]

include hsq in
theorem sq_toLinearMap : ∀ x, A.toLinearMap (A.toLinearMap x) = c₀ • x := hsq

variable [Fact (¬ IsSquare c₀)]

@[expose] def bilinE (Q : QuadraticForm K V) (hc₀ : c₀ ≠ 0)
    (hadj : ∀ x y, Q.polarBilin (A.toLinearMap x) y = Q.polarBilin x (A.toLinearMap y)) :
    letI := modE A c₀ hsq
    LinearMap.BilinForm (extension c₀) V :=
  letI := modE A c₀ hsq
  letI := isScalarTower A c₀ hsq
  positiveBilinear Q.polarBilin A.toLinearMap c₀ QuadraticAlgebra.omega hc₀
    (by rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]; simp)
    (sq_toLinearMap A c₀ hsq) (omega_smul A c₀ hsq) (span_omega c₀) hadj

@[expose] def formE (Q : QuadraticForm K V) (hc₀ : c₀ ≠ 0)
    (hadj : ∀ x y, Q.polarBilin (A.toLinearMap x) y = Q.polarBilin x (A.toLinearMap y)) :
    letI := modE A c₀ hsq
    QuadraticForm (extension c₀) V :=
  letI := modE A c₀ hsq
  quadraticOfPolar (bilinE A c₀ hsq Q hc₀ hadj)

variable (Q : QuadraticForm K V) (hc₀ : c₀ ≠ 0)
  (hadj : ∀ x y, Q.polarBilin (A.toLinearMap x) y = Q.polarBilin x (A.toLinearMap y))

theorem bilinE_apply (x y : V) :
    letI := modE A c₀ hsq
    bilinE A c₀ hsq Q hc₀ hadj x y = algebraMap K (extension c₀) (Q.polarBilin x y) +
      algebraMap K (extension c₀) (c₀⁻¹ * Q.polarBilin (A x) y) * QuadraticAlgebra.omega :=
  rfl

theorem bilinE_isSymm :
    letI := modE A c₀ hsq
    (bilinE A c₀ hsq Q hc₀ hadj).IsSymm := by
  let := modE A c₀ hsq
  let := isScalarTower A c₀ hsq
  exact positiveBilinear_isSymm Q.polarBilin A.toLinearMap c₀ QuadraticAlgebra.omega hc₀ _
    (sq_toLinearMap A c₀ hsq) (omega_smul A c₀ hsq) (span_omega c₀) hadj
    (LinearMap.BilinForm.isSymm_iff.mpr (originalPolar_isSymm Q))

variable (h2 : (2 : K) ≠ 0)

omit [AddCommGroup V] [Module K V] in
include h2 in
theorem two_ne_zero_E : (2 : extension c₀) ≠ 0 := by
  intro h
  apply h2
  have := congrArg QuadraticAlgebra.re h
  rwa [QuadraticAlgebra.re_ofNat] at this

include h2 in
theorem re_formE (x : V) :
    letI := modE A c₀ hsq
    (formE A c₀ hsq Q hc₀ hadj x).re = Q x := by
  let := modE A c₀ hsq
  change ((2 : extension c₀)⁻¹ * bilinE A c₀ hsq Q hc₀ hadj x x).re = Q x
  have h2inv : (2 : extension c₀)⁻¹ = algebraMap K (extension c₀) (2⁻¹) := by
    rw [map_inv₀, map_ofNat]
  rw [h2inv, bilinE_apply]
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.im_mul, mul_zero,
    add_zero, zero_mul, mul_one]
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul]
  field_simp
  ring

include h2 in
theorem formE_nondegenerate (hQ : Q.polarBilin.Nondegenerate) :
    letI := modE A c₀ hsq
    (formE A c₀ hsq Q hc₀ hadj).polarBilin.Nondegenerate := by
  let := modE A c₀ hsq
  let := isScalarTower A c₀ hsq
  exact quadraticOfPolar_nondegenerate _ (bilinE_isSymm A c₀ hsq Q hc₀ hadj)
    (two_ne_zero_E c₀ h2)
    (positiveBilinear_nondegenerate Q.polarBilin A.toLinearMap c₀ QuadraticAlgebra.omega hc₀ _
      (sq_toLinearMap A c₀ hsq) (omega_smul A c₀ hsq) (span_omega c₀) hadj
      (QuadraticAlgebra.basis c₀ 0) (QuadraticAlgebra.basis_apply_zero c₀ 0)
      (QuadraticAlgebra.basis_apply_one (a := c₀) (b := (0 : K))) hQ)

include h2 in
theorem mem_orthogonalGroup_formE (g : V ≃ₗ[K] V) (hg : ∀ x, g (A x) = A (g x))
    (hgQ : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    letI := modE A c₀ hsq
    toE A c₀ hsq g hg ∈ TauCeti.QuadraticMap.orthogonalGroup (formE A c₀ hsq Q hc₀ hadj) := by
  let := modE A c₀ hsq
  let := isScalarTower A c₀ hsq
  apply (quadraticOfPolar_isometry_iff _ (bilinE_isSymm A c₀ hsq Q hc₀ hadj)
    (two_ne_zero_E c₀ h2) _).mpr
  change ∀ x y, positiveFormula Q.polarBilin A.toLinearMap c₀ QuadraticAlgebra.omega (g x) (g y) =
    positiveFormula Q.polarBilin A.toLinearMap c₀ QuadraticAlgebra.omega x y
  exact (positiveFormula_isometry_iff Q.polarBilin A.toLinearMap c₀ QuadraticAlgebra.omega
    (QuadraticAlgebra.basis c₀ 0) (QuadraticAlgebra.basis_apply_zero c₀ 0)
    (QuadraticAlgebra.basis_apply_one (a := c₀) (b := (0 : K))) g hg).mpr
      ((originalQuadratic_isometry_iff Q h2 g).mp hgQ)

include h2 in
theorem ofE_mem_orthogonalGroup :
    letI := modE A c₀ hsq
    ∀ g : V ≃ₗ[extension c₀] V,
      g ∈ TauCeti.QuadraticMap.orthogonalGroup (formE A c₀ hsq Q hc₀ hadj) →
        ofE A c₀ hsq g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  let := modE A c₀ hsq
  let := isScalarTower A c₀ hsq
  intro g hg
  apply (originalQuadratic_isometry_iff Q h2 _).mpr
  apply (positiveFormula_isometry_iff Q.polarBilin A.toLinearMap c₀ QuadraticAlgebra.omega
    (QuadraticAlgebra.basis c₀ 0) (QuadraticAlgebra.basis_apply_zero c₀ 0)
    (QuadraticAlgebra.basis_apply_one (a := c₀) (b := (0 : K))) (ofE A c₀ hsq g)
    (ofE_comm A c₀ hsq g)).mp
  exact (quadraticOfPolar_isometry_iff _ (bilinE_isSymm A c₀ hsq Q hc₀ hadj)
    (two_ne_zero_E c₀ h2) g).mp hg

include h2 in
@[expose] def centEquivE :
    letI := modE A c₀ hsq
    orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (formE A c₀ hsq Q hc₀ hadj) := by
  letI := modE A c₀ hsq
  exact {
    toFun := fun g => ⟨toE A c₀ hsq g.val.val g.property,
      mem_orthogonalGroup_formE A c₀ hsq Q hc₀ hadj h2 _ g.property g.val.property⟩
    invFun := fun g => ⟨⟨ofE A c₀ hsq g.val, ofE_mem_orthogonalGroup A c₀ hsq Q hc₀ hadj h2 _
      g.property⟩, ofE_comm A c₀ hsq g.val⟩
    left_inv := fun g => by apply Subtype.ext; apply Subtype.ext; ext x; rfl
    right_inv := fun g => by apply Subtype.ext; ext x; rfl
    map_mul' := fun g g' => by apply Subtype.ext; ext x; rfl }

theorem centEquivE_symm_apply :
    letI := modE A c₀ hsq
    ∀ (g : TauCeti.QuadraticMap.orthogonalGroup (formE A c₀ hsq Q hc₀ hadj)) (x : V),
      ((centEquivE A c₀ hsq Q hc₀ hadj h2).symm g).val.val x = g.val x := by
  intros
  rfl

theorem finrank_E :
    letI := modE A c₀ hsq
    finrank K V = 2 * finrank (extension c₀) V := by
  let := modE A c₀ hsq
  let := isScalarTower A c₀ hsq
  rw [← Module.finrank_mul_finrank K (extension c₀) V, QuadraticAlgebra.finrank_eq_two]

include h2 in
theorem formE_not_split (hdim : finrank K V = 8) (hnp : ¬ IsPlusType Q) :
    letI := modE A c₀ hsq
    ¬ ∃ S : Submodule (extension c₀) V, finrank (extension c₀) S = 2 ∧
      ∀ x ∈ S, formE A c₀ hsq Q hc₀ hadj x = 0 := by
  let := modE A c₀ hsq
  let := isScalarTower A c₀ hsq
  rintro ⟨S, hS2, hSQ⟩
  apply hnp
  refine ⟨S.restrictScalars K, ?_, fun x hx => ?_⟩
  · have h1 : finrank K (S.restrictScalars K) = finrank K (extension c₀) *
        finrank (extension c₀) S := (Module.finrank_mul_finrank K (extension c₀) S).symm
    rw [h1, hS2, QuadraticAlgebra.finrank_eq_two, hdim]
  · rw [← re_formE A c₀ hsq Q hc₀ hadj h2 x, hSQ x hx]
    rfl

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
