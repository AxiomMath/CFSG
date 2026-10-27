module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareNegativeAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareEigenspaces

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem negative_quadratic_sum (Q : QuadraticForm K V) (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hadj : ∀ x y : V, Q.polarBilin (T x) y = -Q.polarBilin x (T y))
    (x : T.eigenspace b) (y : T.eigenspace (-b)) :
    Q (x.val + y.val) = Q.polarBilin x.val y.val := by
  rw [QuadraticMap.map_add Q x.val y.val,
    negative_adjoint_eigenspace_singular Q T b hb h2 hadj x.val x.property,
    negative_adjoint_eigenspace_singular Q T (-b) (neg_ne_zero.mpr hb)
      h2 hadj y.val y.property, zero_add, zero_add]
  rfl

variable [FiniteDimensional K V]

variable (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
  (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
  (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
  (hadj : ∀ x y : V, Q.polarBilin (T x) y = -Q.polarBilin x (T y))

@[expose] def negativeLinearExtension (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) :
    operatorCentralizer T :=
  splitCentralizerExtension T b hb h2 hsquare
    (f, negativeEigenspaceDual Q.polarBilin hQ T b hb h2 hsquare hadj f)

theorem negativeLinearExtension_apply (f : T.eigenspace b ≃ₗ[K] T.eigenspace b)
    (x : T.eigenspace b) (y : T.eigenspace (-b)) :
    (negativeLinearExtension Q hQ T b hb h2 hsquare hadj f).val (x.val + y.val) =
      (f x).val + (negativeEigenspaceDual Q.polarBilin hQ T b hb h2 hsquare hadj f y).val :=
  splitCentralizerExtension_apply T b hb h2 hsquare _ (x, y)

theorem negativeLinearExtension_preserves_quadratic
    (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) (z : V) :
    Q ((negativeLinearExtension Q hQ T b hb h2 hsquare hadj f).val z) = Q z := by
  obtain ⟨xy, rfl⟩ := (squareScalar_eigenspaceEquiv T b hb h2 hsquare).surjective z
  change Q ((negativeLinearExtension Q hQ T b hb h2 hsquare hadj f).val
      (xy.1.val + xy.2.val)) = Q (xy.1.val + xy.2.val)
  rw [negativeLinearExtension_apply, negative_quadratic_sum Q T b hb h2 hadj,
    negative_quadratic_sum Q T b hb h2 hadj]
  exact negativeEigenspaceDual_preserves Q.polarBilin hQ T b hb h2 hsquare hadj f xy.1 xy.2

@[expose] def negativeOrthogonalExtension (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) :
    orthogonalOperatorCentralizer Q T :=
  ⟨⟨(negativeLinearExtension Q hQ T b hb h2 hsquare hadj f).val,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      (negativeLinearExtension_preserves_quadratic Q hQ T b hb h2 hsquare hadj f)⟩,
    (negativeLinearExtension Q hQ T b hb h2 hsquare hadj f).property⟩

theorem negativeOrthogonalExtension_apply (f : T.eigenspace b ≃ₗ[K] T.eigenspace b)
    (x : T.eigenspace b) (y : T.eigenspace (-b)) :
    (negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj f).val.val (x.val + y.val) =
      (f x).val + (negativeEigenspaceDual Q.polarBilin hQ T b hb h2 hsquare hadj f y).val :=
  negativeLinearExtension_apply Q hQ T b hb h2 hsquare hadj f x y

theorem negativeOrthogonalExtension_positive (f : T.eigenspace b ≃ₗ[K] T.eigenspace b)
    (x : T.eigenspace b) :
    (negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj f).val.val x.val = (f x).val := by
  simpa using negativeOrthogonalExtension_apply Q hQ T b hb h2 hsquare hadj f x 0

theorem negativeOrthogonalExtension_negative (f : T.eigenspace b ≃ₗ[K] T.eigenspace b)
    (y : T.eigenspace (-b)) :
    (negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj f).val.val y.val =
      (negativeEigenspaceDual Q.polarBilin hQ T b hb h2 hsquare hadj f y).val := by
  simpa using negativeOrthogonalExtension_apply Q hQ T b hb h2 hsquare hadj f 0 y

theorem negativeOrthogonalExtension_preserves_polar
    (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) (x y : V) :
    Q.polarBilin ((negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj f).val.val x)
      ((negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj f).val.val y) =
      Q.polarBilin x y :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj f).val.property x y

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative
