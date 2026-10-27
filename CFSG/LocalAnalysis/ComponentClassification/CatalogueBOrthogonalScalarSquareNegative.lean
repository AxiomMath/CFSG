module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareNegativeExtension

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def negativeCentralizerRestriction (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) : orthogonalOperatorCentralizer Q T →*
      (T.eigenspace b ≃ₗ[K] T.eigenspace b) :=
  (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype)).subtype.comp
    (orthogonalCentralizerRestriction Q T b)

theorem negativeCentralizerRestriction_apply (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (g : orthogonalOperatorCentralizer Q T)
    (x : T.eigenspace b) :
    (negativeCentralizerRestriction Q T b g x).val = g.val.val x.val := rfl

variable [FiniteDimensional K V]

variable (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
  (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
  (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
  (hadj : ∀ x y : V, Q.polarBilin (T x) y = -Q.polarBilin x (T y))

theorem negativeCentralizer_negative_restriction (g : orthogonalOperatorCentralizer Q T) :
    operatorCentralizerRestriction T (-b) (orthogonalCentralizerToOperator Q T g) =
      negativeEigenspaceDual Q.polarBilin hQ T b hb h2 hsquare hadj
        (negativeCentralizerRestriction Q T b g) := by
  apply negativeEigenspaceDual_unique Q.polarBilin hQ T b hb h2 hsquare hadj
  intro x y
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.val.property x.val y.val

theorem negativeCentralizer_negative_action (g : orthogonalOperatorCentralizer Q T)
    (y : T.eigenspace (-b)) :
    g.val.val y.val =
      (negativeEigenspaceDual Q.polarBilin hQ T b hb h2 hsquare hadj
        (negativeCentralizerRestriction Q T b g) y).val := by
  exact congrArg (fun f : T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b) => (f y).val)
    (negativeCentralizer_negative_restriction Q hQ T b hb h2 hsquare hadj g)

theorem negativeCentralizerRestriction_extension (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) :
    negativeCentralizerRestriction Q T b
      (negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj f) = f := by
  ext x
  exact negativeOrthogonalExtension_positive Q hQ T b hb h2 hsquare hadj f x

theorem negativeOrthogonalExtension_restriction (g : orthogonalOperatorCentralizer Q T) :
    negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj
      (negativeCentralizerRestriction Q T b g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  ext z
  obtain ⟨xy, rfl⟩ := (squareScalar_eigenspaceEquiv T b hb h2 hsquare).surjective z
  change (negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj
      (negativeCentralizerRestriction Q T b g)).val.val (xy.1.val + xy.2.val) =
    g.val.val (xy.1.val + xy.2.val)
  rw [negativeOrthogonalExtension_apply, map_add]
  congr 1
  exact (negativeCentralizer_negative_action Q hQ T b hb h2 hsquare hadj g xy.2).symm

@[expose] def negativeCentralizerEquiv : orthogonalOperatorCentralizer Q T ≃*
    (T.eigenspace b ≃ₗ[K] T.eigenspace b) where
  toFun := negativeCentralizerRestriction Q T b
  invFun := negativeOrthogonalExtension Q hQ T b hb h2 hsquare hadj
  left_inv := negativeOrthogonalExtension_restriction Q hQ T b hb h2 hsquare hadj
  right_inv := negativeCentralizerRestriction_extension Q hQ T b hb h2 hsquare hadj
  map_mul' := (negativeCentralizerRestriction Q T b).map_mul

theorem negativeCentralizerEquiv_apply (g : orthogonalOperatorCentralizer Q T)
    (x : T.eigenspace b) :
    (negativeCentralizerEquiv Q hQ T b hb h2 hsquare hadj g x).val = g.val.val x.val := rfl

theorem negativeCentralizerEquiv_symm_positive
    (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) (x : T.eigenspace b) :
    ((negativeCentralizerEquiv Q hQ T b hb h2 hsquare hadj).symm f).val.val x.val =
      (f x).val :=
  negativeOrthogonalExtension_positive Q hQ T b hb h2 hsquare hadj f x

theorem negativeCentralizerEquiv_symm_negative
    (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) (y : T.eigenspace (-b)) :
    ((negativeCentralizerEquiv Q hQ T b hb h2 hsquare hadj).symm f).val.val y.val =
      (negativeEigenspaceDual Q.polarBilin hQ T b hb h2 hsquare hadj f y).val :=
  negativeOrthogonalExtension_negative Q hQ T b hb h2 hsquare hadj f y

include hQ hb h2 hsquare hadj in
theorem negative_square_centralizer_structure :
    IsCompl (T.eigenspace b) (T.eigenspace (-b)) ∧
      (∀ x ∈ T.eigenspace b, Q x = 0) ∧
      (∀ x ∈ T.eigenspace (-b), Q x = 0) ∧
      (crossPairing Q.polarBilin (T.eigenspace b) (T.eigenspace (-b))).IsPerfPair ∧
      Module.finrank K (T.eigenspace b) = Module.finrank K (T.eigenspace (-b)) ∧
      Module.finrank K (T.eigenspace b) = Module.finrank K V / 2 ∧
      Module.finrank K (T.eigenspace (-b)) = Module.finrank K V / 2 ∧
      Nonempty (orthogonalOperatorCentralizer Q T ≃*
        (T.eigenspace b ≃ₗ[K] T.eigenspace b)) := by
  have hs := negative_adjoint_both_eigenspaces_singular Q T b hb h2 hadj
  have hd := negative_adjoint_eigenspace_half_dimensions Q.polarBilin hQ T b hb h2 hsquare hadj
  exact ⟨squareScalar_eigenspaces_isCompl T b hb h2 hsquare, hs.1, hs.2,
    negative_eigenspaces_perfect Q.polarBilin hQ T b hb h2 hsquare hadj,
    hd.1, hd.2.1, hd.2.2, ⟨negativeCentralizerEquiv Q hQ T b hb h2 hsquare hadj⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative
