module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowOData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.OddSelector (rowOAction rowOAction_val)

variable {k : Type} [Field k]

@[expose] def g1 (δ : k) (i : k) (hi : i * i = -1) : SpecialLinearGroup (Fin 2) (extension δ) :=
  ⟨!![algebraMap k (extension δ) i, 0; 0, -algebraMap k (extension δ) i], by
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_neg, ← map_mul, hi, map_neg, map_one,
      neg_neg]⟩

theorem coe_g1 (δ : k) (i : k) (hi : i * i = -1) :
    ((g1 δ i hi : SpecialLinearGroup (Fin 2) (extension δ)) :
      Matrix (Fin 2) (Fin 2) (extension δ)) =
      !![algebraMap k (extension δ) i, 0; 0, -algebraMap k (extension δ) i] := rfl

theorem g1_mul_self (δ : k) (i : k) (hi : i * i = -1) : g1 δ i hi * g1 δ i hi = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  refine Matrix.ext fun a j => ?_
  fin_cases a <;> fin_cases j <;>
    simp [g1, Matrix.mul_apply, Fin.sum_univ_two, ← map_mul, hi]

theorem coord_g1 (δ : kˣ) (h2 : (2 : k) ≠ 0) (i : k) (hi : i * i = -1) (x : Fin 4 → k) :
    (hermitianCoordinates (δ : k) h2).symm
        (rowOAction δ (g1 (δ : k) i hi) (hermitianCoordinates (δ : k) h2 x)) =
      ![-x 0, -x 1, x 2, x 3] := by
  rw [hermitianCoordinates_symm_apply, rowOAction_val, hermitianCoordinates_val, coe_g1]
  have hstar : star (algebraMap k (extension (δ : k)) i) = algebraMap k (extension (δ : k)) i :=
    (conjugation (δ : k)).commutes i
  have key : ∀ y : k, algebraMap k (extension (δ : k)) i * algebraMap k (extension (δ : k)) y *
      algebraMap k (extension (δ : k)) i = algebraMap k (extension (δ : k)) (-y) := fun y => by
    rw [← map_mul, ← map_mul]
    congr 1
    linear_combination y * hi
  have key' : ∀ z : extension (δ : k), algebraMap k (extension (δ : k)) i * z *
      -algebraMap k (extension (δ : k)) i = z := fun z => by
    rw [mul_neg, mul_comm _ z, mul_assoc, ← map_mul, hi, map_neg, map_one]
    ring
  funext j
  fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, star_zero, star_neg, hstar, mul_zero, zero_mul,
      add_zero, zero_add, Fin.zero_eta]
    rw [key]
    simp [QuadraticAlgebra.algebraMap_re]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, star_zero, star_neg, hstar, mul_zero, zero_mul,
      add_zero, zero_add, Fin.mk_one, neg_mul, mul_neg, neg_neg]
    rw [key]
    simp [QuadraticAlgebra.algebraMap_re]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, star_zero, star_neg, hstar, mul_zero, zero_mul,
      add_zero, zero_add, Fin.reduceFinMk, Matrix.cons_val]
    rw [key']
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, star_zero, star_neg, hstar, mul_zero, zero_mul,
      add_zero, zero_add, Fin.reduceFinMk, Matrix.cons_val]
    rw [key']

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
