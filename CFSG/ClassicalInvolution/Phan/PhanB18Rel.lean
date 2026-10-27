module

public import CFSG.ClassicalInvolution.Phan.PhanB17Mat
public import CFSG.ClassicalInvolution.Phan.PhanB15Hom

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock mat_longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

section Poly

variable {F : Type} [Field F]

theorem rel_B1 (t c d x0 x1 y0 y1 : F) (ht : 2 * t = 1) :
    Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (conjD2 t (nuMat c (-d) x0 x1 0 0)) *
        twMat t (nuMat c d y0 y1 0 0) =
      twMat t (nuMat c d y0 y1 0 0) *
        Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
          (conjD2 t (nuMat c (-d) x0 x1 0 0)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Sp.blockMat, twMat, conjD2, nuMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.one_apply] <;> grind

theorem rel_B2 (t c d x0 x1 a1 a2 b1 b2 : F) (ht : 2 * t = 1) (hx : x0 * x0 + x1 * x1 = 1) :
    Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2)) (conjD2 t (nuMat c (-d) x0 x1 0 0)) *
        twMat t (nuMat c d a1 a2 b1 b2) =
      twMat t (nuMat c d a1 a2 (x0 * b1 + x1 * b2) (x0 * b2 - x1 * b1)) *
        Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
          (conjD2 t (nuMat c (-d) x0 x1 0 0)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Sp.blockMat, twMat, conjD2, nuMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.one_apply] <;> grind

theorem rel_B3 (t c d y0 y1 a1 a2 b1 b2 : F) (ht : 2 * t = 1) (hy : y0 * y0 + y1 * y1 = 1) :
    twMat t (nuMat c d y0 y1 0 0) *
        Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
          (conjD2 t (nuMat c (-d) a1 a2 b1 b2)) =
      Sp.blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
          (conjD2 t (nuMat c (-d) a1 a2 ((y0 * y0 - y1 * y1) * b1 - (-(2 * y0 * y1)) * b2)
            ((y0 * y0 - y1 * y1) * b2 + (-(2 * y0 * y1)) * b1))) *
        twMat t (nuMat c d y0 y1 0 0) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Sp.blockMat, twMat, conjD2, nuMat, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks, Matrix.one_apply] <;> grind

end Poly

end CFSG.ClassicalInvolution.PhanB3
