module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8q
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8a
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8p
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUf

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.OddSelector (rowOAction)

variable {K : Type} [Field K] {b c : K} (c₀ : K) [Fact (¬ IsSquare c₀)]
  (δ : (extension c₀)ˣ) (h2 : (2 : extension c₀) ≠ 0) (d : (extension c₀)ˣ)
  (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))

@[expose] def xi : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀) := χ.trans (scaleD c₀ d)

omit [Fact (¬ IsSquare c₀)] in
theorem xi_apply (v : Fin (2 * 4) → K) :
    xi c₀ d χ v = ![(d : extension c₀) * χ v 0, χ v 1, χ v 2, χ v 3] := rfl

variable (hQd : ∀ v, Q8 K b c v = ((d : extension c₀) * OIL.qf (δ : extension c₀) (χ v)).re)

include hQd in
theorem Q_xi (v : Fin (2 * 4) → K) :
    Q8 K b c v = (xi c₀ d χ v 0 * xi c₀ d χ v 1).re +
      ((d : extension c₀) *
        (-(xi c₀ d χ v 2) ^ 2 + (δ : extension c₀) * xi c₀ d χ v 3 ^ 2)).re := by
  rw [hQd, xi_apply, OIL.qf, ← QuadraticAlgebra.re_add]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

include hQd in
theorem Q_xi_hyp (u : Fin (2 * 4) → K) (h2u : xi c₀ d χ u 2 = 0) (h3u : xi c₀ d χ u 3 = 0) :
    Q8 K b c u = (xi c₀ d χ u 0 * xi c₀ d χ u 1).re := by
  rw [Q_xi c₀ δ d χ hQd, h2u, h3u]
  simp

include hQd in
theorem polar_xi (v u : Fin (2 * 4) → K) (h2u : xi c₀ d χ u 2 = 0) (h3u : xi c₀ d χ u 3 = 0) :
    polar (Q8 K b c) v u =
      (xi c₀ d χ v 0 * xi c₀ d χ u 1 + xi c₀ d χ u 0 * xi c₀ d χ v 1).re := by
  rw [polar, Q_xi c₀ δ d χ hQd, Q_xi c₀ δ d χ hQd v, Q_xi_hyp c₀ δ d χ hQd u h2u h3u, map_add]
  simp only [Pi.add_apply, h2u, h3u, add_zero]
  have e : (xi c₀ d χ v 0 + xi c₀ d χ u 0) * (xi c₀ d χ v 1 + xi c₀ d χ u 1) =
      xi c₀ d χ v 0 * xi c₀ d χ v 1 +
        (xi c₀ d χ v 0 * xi c₀ d χ u 1 + xi c₀ d χ u 0 * xi c₀ d χ v 1) +
        xi c₀ d χ u 0 * xi c₀ d χ u 1 := by ring
  rw [e, QuadraticAlgebra.re_add, QuadraticAlgebra.re_add, QuadraticAlgebra.re_add]
  ring

omit [Fact (¬ IsSquare c₀)] in
theorem xi_A (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
    (hχA : ∀ v, χ (A v) = (QuadraticAlgebra.omega : extension c₀) • χ v) (v : Fin (2 * 4) → K) :
    xi c₀ d χ (A v) = (QuadraticAlgebra.omega : extension c₀) • xi c₀ d χ v := by
  rw [xi_apply, xi_apply, hχA]
  funext j
  fin_cases j <;> simp [mul_left_comm]

theorem xi_z1 (i : extension c₀) (hi : i * i = -1)
    (z : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
    (hz : ∀ v, z v = χ.symm ((OIU.Umat δ h2 (g1 (δ : extension c₀) i hi) :
      Matrix (Fin 4) (Fin 4) (extension c₀)) *ᵥ χ v)) (v : Fin (2 * 4) → K) :
    xi c₀ d χ (z v) = ![-xi c₀ d χ v 0, -xi c₀ d χ v 1, xi c₀ d χ v 2, xi c₀ d χ v 3] := by
  rw [xi_apply, xi_apply, hz, LinearEquiv.apply_symm_apply, OIU.Umat_mulVec, coord_g1]
  funext j
  fin_cases j <;> simp

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
