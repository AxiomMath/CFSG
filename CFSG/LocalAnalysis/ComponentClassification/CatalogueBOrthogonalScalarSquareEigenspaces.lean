module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareBasic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionEigenspaces

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem restriction_nondegenerate_of_complements
    (B : _root_.LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hsym : B.IsSymm)
    (U W : Submodule K V) (hcomp : IsCompl U W)
    (horth : ∀ x ∈ U, ∀ y ∈ W, B x y = 0) : (B.restrict U).Nondegenerate := by
  have hl : (B.restrict U).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hB.1
    intro y
    obtain ⟨u, w, hu, hw, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hcomp.codisjoint y
    change B x.val (u + w) = 0
    rw [BilinForm.add_right, horth x.val x.property w hw, add_zero]
    exact hx ⟨u, hu⟩
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  change B x.val y.val = 0
  rw [hsym.eq]
  exact hx y

theorem positive_adjoint_eigenspaces_nondegenerate
    (B : _root_.LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hsym : B.IsSymm)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, B (T x) y = B x (T y)) :
    (B.restrict (T.eigenspace b)).Nondegenerate ∧
      (B.restrict (T.eigenspace (-b))).Nondegenerate := by
  have hc := CatalogueBProjectiveInvolution.squareScalar_eigenspaces_isCompl
    T b hb h2 hsquare
  have ho := opposite_eigenspaces_orthogonal B T b hb h2 hadj
  constructor
  · exact restriction_nondegenerate_of_complements B hB hsym _ _ hc
      (fun x hx y hy => ho x y hx hy)
  · exact restriction_nondegenerate_of_complements B hB hsym _ _ hc.symm
      (fun x hx y hy => (hsym.eq x y).trans (ho y x hy hx))

theorem negative_adjoint_eigenspace_singular (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = -Q.polarBilin x (T y))
    (x : V) (hx : x ∈ T.eigenspace b) : Q x = 0 := by
  have hz := same_eigenspace_isotropic Q.polarBilin T b hb h2 hadj x x hx hx
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
    ← two_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left h2

theorem negative_adjoint_both_eigenspaces_singular (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = -Q.polarBilin x (T y)) :
    (∀ x ∈ T.eigenspace b, Q x = 0) ∧
      (∀ x ∈ T.eigenspace (-b), Q x = 0) :=
  ⟨fun x hx => negative_adjoint_eigenspace_singular Q T b hb h2 hadj x hx,
    fun x hx => negative_adjoint_eigenspace_singular Q T (-b) (neg_ne_zero.mpr hb)
      h2 hadj x hx⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
