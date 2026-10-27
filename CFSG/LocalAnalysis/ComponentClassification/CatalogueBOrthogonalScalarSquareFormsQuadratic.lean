module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFormsBilinear
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

universe u v w

variable {E : Type v} {V : Type w} [Field E] [AddCommGroup V] [Module E V]

@[expose] def quadraticOfPolar (B : LinearMap.BilinForm E V) : QuadraticForm E V :=
  (2 : E)⁻¹ • B.toQuadraticMap

theorem quadraticOfPolar_apply (B : LinearMap.BilinForm E V) (x : V) :
    quadraticOfPolar B x = B x x / 2 := by
  change (2 : E)⁻¹ * B x x = B x x / 2
  rw [div_eq_mul_inv, mul_comm]

theorem quadraticOfPolar_polar (B : LinearMap.BilinForm E V) (hB : B.IsSymm)
    (h2 : (2 : E) ≠ 0) (x y : V) :
    QuadraticMap.polar (quadraticOfPolar B) x y = B x y := by
  have hi : (2 : E)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  rw [QuadraticMap.polar, quadraticOfPolar_apply, quadraticOfPolar_apply,
    quadraticOfPolar_apply]
  simp only [map_add, LinearMap.add_apply, hB.eq y x, div_eq_mul_inv]
  linear_combination B x y * hi

theorem quadraticOfPolar_polarBilin (B : LinearMap.BilinForm E V) (hB : B.IsSymm)
    (h2 : (2 : E) ≠ 0) : (quadraticOfPolar B).polarBilin = B := by
  ext x y
  exact quadraticOfPolar_polar B hB h2 x y

theorem quadraticOfPolar_nondegenerate (B : LinearMap.BilinForm E V) (hB : B.IsSymm)
    (h2 : (2 : E) ≠ 0) (hnd : B.Nondegenerate) :
    (quadraticOfPolar B).polarBilin.Nondegenerate := by
  rw [quadraticOfPolar_polarBilin B hB h2]
  exact hnd

theorem quadraticOfPolar_isometry_iff (B : LinearMap.BilinForm E V) (hB : B.IsSymm)
    (h2 : (2 : E) ≠ 0) (g : V ≃ₗ[E] V) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadraticOfPolar B) ↔
      ∀ x y, B (g x) (g y) = B x y := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar
    ((isUnit_iff_ne_zero.mpr h2).isSMulRegular E)]
  simp only [quadraticOfPolar_polar B hB h2]

variable {K : Type u} [Field K] [Algebra K E] [Module K V]

omit [Module E V] in
theorem positiveFormula_isometry_iff (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (s : E) (b : Module.Basis (Fin 2) K E)
    (h0 : b 0 = 1) (h1 : b 1 = s) (g : V → V)
    (hcomm : ∀ x, g (T x) = T (g x)) :
    (∀ x y, positiveFormula B T d s (g x) (g y) = positiveFormula B T d s x y) ↔
      ∀ x y, B (g x) (g y) = B x y := by
  constructor
  · intro hg x y
    exact ((coordinate_equality b s h0 h1
      (B (g x) (g y)) (d⁻¹ * B (T (g x)) (g y)) (B x y) (d⁻¹ * B (T x) y)).mp
        (hg x y)).1
  · intro hg x y
    simp only [positiveFormula, ← hcomm, hg]

omit [Module E V] in
theorem negativeFormula_isometry_iff (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (s : E) (b : Module.Basis (Fin 2) K E)
    (h0 : b 0 = 1) (h1 : b 1 = s) (g : V → V)
    (hcomm : ∀ x, g (T x) = T (g x)) :
    (∀ x y, negativeFormula B T d s (g x) (g y) = negativeFormula B T d s x y) ↔
      ∀ x y, B (g x) (g y) = B x y := by
  constructor
  · intro hg x y
    exact ((coordinate_equality b s h0 h1
      (B (g x) (g y)) (d⁻¹ * B (g x) (T (g y))) (B x y) (d⁻¹ * B x (T y))).mp
        (hg x y)).1
  · intro hg x y
    simp only [negativeFormula, ← hcomm, hg]

theorem originalPolar_isSymm (Q : QuadraticForm K V) : Q.polarBilin.IsSymm :=
  ⟨fun x y => QuadraticMap.polar_comm Q x y⟩

theorem originalQuadratic_isometry_iff (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (g : V ≃ₗ[K] V) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ↔
      ∀ x y, Q.polarBilin (g x) (g y) = Q.polarBilin x y := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar
    ((isUnit_iff_ne_zero.mpr h2).isSMulRegular K)]
  rfl

theorem extension_two_ne_zero (h2 : (2 : K) ≠ 0) : (2 : E) ≠ 0 := by
  have h := (algebraMap K E).injective.ne h2
  simpa only [map_ofNat, map_zero] using h

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
