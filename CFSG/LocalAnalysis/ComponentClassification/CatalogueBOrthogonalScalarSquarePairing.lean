module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionEigenspaces

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def crossPairing (B : _root_.LinearMap.BilinForm K V)
    (U W : Submodule K V) : U →ₗ[K] W →ₗ[K] K :=
  B.compl₁₂ U.subtype W.subtype

theorem crossPairing_nondegenerate (B : _root_.LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (U W : Submodule K V) (hcomp : IsCompl U W)
    (hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 0)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    (crossPairing B U W).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    apply hB.1
    intro y
    obtain ⟨u, w, hu, hw, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hcomp.codisjoint y
    change B x.val (u + w) = 0
    rw [BilinForm.add_right, hU x.val x.property u hu, zero_add]
    exact hx ⟨w, hw⟩
  · intro y hy
    apply Subtype.ext
    apply hB.2
    intro x
    obtain ⟨u, w, hu, hw, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hcomp.codisjoint x
    change B (u + w) y.val = 0
    rw [BilinForm.add_left, hW w hw y.val y.property, add_zero]
    exact hy ⟨u, hu⟩

variable [FiniteDimensional K V]

theorem crossPairing_perfect (B : _root_.LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (U W : Submodule K V) (hcomp : IsCompl U W)
    (hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 0)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    (crossPairing B U W).IsPerfPair := by
  have h := crossPairing_nondegenerate B hB U W hcomp hU hW
  apply LinearMap.IsPerfPair.of_injective
  · exact LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1)
  · exact LinearMap.ker_eq_bot.mp (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp h.2)

theorem crossPairing_finrank_eq (B : _root_.LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (U W : Submodule K V) (hcomp : IsCompl U W)
    (hU : ∀ x ∈ U, ∀ y ∈ U, B x y = 0)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    Module.finrank K U = Module.finrank K W := by
  let : (crossPairing B U W).IsPerfPair := crossPairing_perfect B hB U W hcomp hU hW
  exact ((crossPairing B U W).toPerfPair.finrank_eq).trans Subspace.dual_finrank_eq

theorem negative_adjoint_eigenspace_half_dimensions
    (B : _root_.LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hadj : ∀ x y : V, B (T x) y = -B x (T y)) :
    Module.finrank K (T.eigenspace b) = Module.finrank K (T.eigenspace (-b)) ∧
      Module.finrank K (T.eigenspace b) = Module.finrank K V / 2 ∧
      Module.finrank K (T.eigenspace (-b)) = Module.finrank K V / 2 := by
  have hc := CatalogueBProjectiveInvolution.squareScalar_eigenspaces_isCompl
    T b hb h2 hsquare
  have hd := crossPairing_finrank_eq B hB _ _ hc
    (fun x hx y hy => same_eigenspace_isotropic B T b hb h2 hadj x y hx hy)
    (fun x hx y hy => same_eigenspace_isotropic B T (-b) (neg_ne_zero.mpr hb)
      h2 hadj x y hx hy)
  have hs := CatalogueBProjectiveInvolution.squareScalar_eigenspace_finrank
    T b hb h2 hsquare
  exact ⟨hd, by omega, by omega⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
