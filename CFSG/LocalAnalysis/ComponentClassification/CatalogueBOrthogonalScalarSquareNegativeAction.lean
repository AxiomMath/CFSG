module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareNegativeDual
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquarePairing

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem negative_eigenspaces_perfect (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, B (T x) y = -B x (T y)) :
    (crossPairing B (T.eigenspace b) (T.eigenspace (-b))).IsPerfPair :=
  crossPairing_perfect B hB _ _
    (CatalogueBProjectiveInvolution.squareScalar_eigenspaces_isCompl T b hb h2 hsquare)
    (fun x hx y hy => same_eigenspace_isotropic B T b hb h2 hadj x y hx hy)
    (fun x hx y hy => same_eigenspace_isotropic B T (-b) (neg_ne_zero.mpr hb)
      h2 hadj x y hx hy)

variable (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
  (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
  (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
  (hadj : ∀ x y : V, B (T x) y = -B x (T y))

@[expose] def negativePairingEquiv :
    T.eigenspace (-b) ≃ₗ[K] Module.Dual K (T.eigenspace b) := by
  letI := negative_eigenspaces_perfect B hB T b hb h2 hsquare hadj
  exact (crossPairing B (T.eigenspace b) (T.eigenspace (-b))).flip.toPerfPair

theorem negativePairingEquiv_apply (y : T.eigenspace (-b)) (x : T.eigenspace b) :
    negativePairingEquiv B hB T b hb h2 hsquare hadj y x = B x.val y.val := rfl

@[expose] def negativeEigenspaceDual (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) :
    T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b) :=
  ((negativePairingEquiv B hB T b hb h2 hsquare hadj).trans f.symm.dualMap).trans
    (negativePairingEquiv B hB T b hb h2 hsquare hadj).symm

theorem negativeEigenspaceDual_pairing (f : T.eigenspace b ≃ₗ[K] T.eigenspace b)
    (x : T.eigenspace b) (y : T.eigenspace (-b)) :
    B x.val (negativeEigenspaceDual B hB T b hb h2 hsquare hadj f y).val =
      B (f.symm x).val y.val := by
  let := negative_eigenspaces_perfect B hB T b hb h2 hsquare hadj
  exact inverseDualAction_pairing
    (crossPairing B (T.eigenspace b) (T.eigenspace (-b))) f x y

theorem negativeEigenspaceDual_preserves (f : T.eigenspace b ≃ₗ[K] T.eigenspace b)
    (x : T.eigenspace b) (y : T.eigenspace (-b)) :
    B (f x).val (negativeEigenspaceDual B hB T b hb h2 hsquare hadj f y).val =
      B x.val y.val := by
  rw [negativeEigenspaceDual_pairing, f.symm_apply_apply]

theorem negativeEigenspaceDual_unique (f : T.eigenspace b ≃ₗ[K] T.eigenspace b)
    (g : T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b))
    (hg : ∀ x y, B (f x).val (g y).val = B x.val y.val) :
    g = negativeEigenspaceDual B hB T b hb h2 hsquare hadj f := by
  let := negative_eigenspaces_perfect B hB T b hb h2 hsquare hadj
  exact inverseDualAction_unique
    (crossPairing B (T.eigenspace b) (T.eigenspace (-b))) f g hg

@[expose] def negativeEigenspaceDualHom :
    (T.eigenspace b ≃ₗ[K] T.eigenspace b) →*
      (T.eigenspace (-b) ≃ₗ[K] T.eigenspace (-b)) := by
  letI := negative_eigenspaces_perfect B hB T b hb h2 hsquare hadj
  exact inverseDualHom (crossPairing B (T.eigenspace b) (T.eigenspace (-b)))

theorem negativeEigenspaceDualHom_apply (f : T.eigenspace b ≃ₗ[K] T.eigenspace b) :
    negativeEigenspaceDualHom B hB T b hb h2 hsquare hadj f =
      negativeEigenspaceDual B hB T b hb h2 hsquare hadj f := rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative
