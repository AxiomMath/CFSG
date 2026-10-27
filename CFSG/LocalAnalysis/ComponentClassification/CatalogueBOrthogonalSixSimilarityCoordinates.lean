module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticWitt

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSixSimilarity

open Matrix QuadraticMap CatalogueBOddQuadratic CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

@[expose] def planesBinaryCoordinates (a delta : Kˣ) :
    ((Fin 2 → K × K) × (Fin 2 → K)) ≃ₗ[K] (Fin 6 → K) where
  toFun x := ![(x.1 0).1, -(x.1 0).2 / (a : K), x.2 0, x.2 1,
    (x.1 1).1, -(x.1 1).2 / ((a : K) * (delta : K))]
  invFun x := (fun i => if i = 0 then (x 0, -(a : K) * x 1)
      else (x 4, -((a : K) * (delta : K)) * x 5), ![x 2, x 3])
  left_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i
      · apply Prod.ext
        · rfl
        · change -(a : K) * (-(x.1 0).2 / (a : K)) = (x.1 0).2
          field_simp
      · apply Prod.ext
        · rfl
        · change -((a : K) * (delta : K)) *
            (-(x.1 1).2 / ((a : K) * (delta : K))) = (x.1 1).2
          field_simp
    · funext i
      fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i
    · rfl
    · change -(-(a : K) * x 1) / (a : K) = x 1
      field_simp
    · rfl
    · rfl
    · rfl
    · change -(-((a : K) * (delta : K)) * x 5) /
        ((a : K) * (delta : K)) = x 5
      field_simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp [add_div]
    all_goals ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]
    all_goals ring

theorem planesBinaryCoordinates_apply (a delta : Kˣ)
    (x : (Fin 2 → K × K) × (Fin 2 → K)) :
    planesBinaryCoordinates a delta x =
      ![(x.1 0).1, -(x.1 0).2 / (a : K), x.2 0, x.2 1,
        (x.1 1).1, -(x.1 1).2 / ((a : K) * (delta : K))] := rfl

theorem planesBinaryCoordinates_form (w : Fin 2 → Kˣ)
    (x : (Fin 2 → K × K) × (Fin 2 → K)) :
    let delta : Kˣ := -(w 1) / w 0
    let y := planesBinaryCoordinates (w 0) delta x
    ((hyperbolicSumForm K 2).prod (weightedSumSquares K w)) x =
      -(w 0 : K) * (y 0 * y 1 - y 2 ^ 2 + (delta : K) * y 3 ^ 2 +
        (delta : K) * y 4 * y 5) := by
  dsimp only
  rw [QuadraticMap.prod_apply, hyperbolicSumForm_apply, Fin.sum_univ_two,
    weightedSumSquares_apply, Fin.sum_univ_two]
  simp only [planesBinaryCoordinates_apply, Units.smul_def, smul_eq_mul,
    Units.val_div_eq_div_val, Units.val_neg]
  change (x.1 0).1 * (x.1 0).2 + (x.1 1).1 * (x.1 1).2 +
      ((w 0 : K) * (x.2 0 * x.2 0) + (w 1 : K) * (x.2 1 * x.2 1)) =
    -(w 0 : K) * ((x.1 0).1 * (-(x.1 0).2 / (w 0 : K)) - x.2 0 ^ 2 +
      (-(w 1 : K) / (w 0 : K)) * x.2 1 ^ 2 +
      (-(w 1 : K) / (w 0 : K)) * (x.1 1).1 *
        (-(x.1 1).2 / ((w 0 : K) * (-(w 1 : K) / (w 0 : K)))))
  field_simp
  ring

theorem binary_tail_extension_norm (w : Fin 2 → Kˣ) (s z : K) :
    let delta : Kˣ := -(w 1) / w 0
    (w 0 : K) * QuadraticAlgebra.norm
        (⟨s, z⟩ : extension (delta : K)) =
      (w 0 : K) * s ^ 2 + (w 1 : K) * z ^ 2 := by
  dsimp only
  rw [extension_norm]
  simp only [Units.val_div_eq_div_val, Units.val_neg]
  field_simp
  ring

end CFSG.ComponentClassification.CatalogueBOrthogonalSixSimilarity
