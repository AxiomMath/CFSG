module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8o

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

variable (c₀ : K) (hc₀ : c₀ ≠ 0) (Q : QuadraticForm K V) (ξ : V ≃ₗ[K] (Fin 4 → extension c₀))
  (hpol : ∀ v u, ξ u 2 = 0 → ξ u 3 = 0 → polar Q v u = (ξ v 0 * ξ u 1 + ξ u 0 * ξ v 1).re)
  (hQu : ∀ u, ξ u 2 = 0 → ξ u 3 = 0 → Q u = (ξ u 0 * ξ u 1).re)

include hpol hQu hc₀ in
theorem reflect_four (h2K : (2 : K) ≠ 0) (v : V) :
    ξ (reflect Q (vw1 c₀ ξ) (reflect Q (vw2 c₀ ξ) (reflect Q (vu1 c₀ ξ)
      (reflect Q (vu2 c₀ ξ) v)))) =
      ![⟨0, -1⟩ * star (ξ v 1), ⟨0, -c₀⁻¹⟩ * star (ξ v 0), ξ v 2, ξ v 3] := by
  rw [reflect_w c₀ hc₀ Q ξ hpol hQu h2K, reflect_u c₀ hc₀ Q ξ hpol hQu]
  simp

@[expose] def scaleD (d : (extension c₀)ˣ) :
    (Fin 4 → extension c₀) ≃ₗ[K] (Fin 4 → extension c₀) where
  toFun x := ![(d : extension c₀) * x 0, x 1, x 2, x 3]
  invFun x := ![((d⁻¹ : (extension c₀)ˣ) : extension c₀) * x 0, x 1, x 2, x 3]
  map_add' x y := by funext i; fin_cases i <;> simp [mul_add]
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [Algebra.smul_def, mul_left_comm]
  left_inv x := by
    funext i
    fin_cases i <;> simp [← mul_assoc]
  right_inv x := by
    funext i
    fin_cases i <;> simp [← mul_assoc]

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
