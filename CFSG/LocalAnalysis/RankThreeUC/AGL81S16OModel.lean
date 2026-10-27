module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONormB

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

abbrev OW (F : Type) : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F

variable {F : Type} [Field F] {b c : F}

@[expose] def xM (w : OW F) : Matrix (Fin 2) (Fin 2) F :=
  !![w (Sum.inl idx0), w (Sum.inl idx1); w (Sum.inr (Sum.inl idx1)), w (Sum.inr (Sum.inl idx0))]

@[expose] def nV (w : OW F) : Fin 2 → F := ![w (Sum.inr (Sum.inr 0)), w (Sum.inr (Sum.inr 1))]

@[expose] def mkW (X : Matrix (Fin 2) (Fin 2) F) (z : Fin 2 → F) : OW F
  | Sum.inl i => X 0 i
  | Sum.inr (Sum.inl i) => X 1 (1 - i)
  | Sum.inr (Sum.inr j) => z j

theorem mkW_xM_nV (w : OW F) : mkW (xM w) (nV w) = w := by
  ext i
  rcases i with i | i | j
  · fin_cases i <;> simp [xM, mkW, idx0, idx1]
  · fin_cases i <;> simp [xM, mkW, idx0, idx1]
  · fin_cases j <;> simp [nV, mkW]

@[expose] def QN (b c : F) (z : Fin 2 → F) : F := z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2

theorem quadMinus_eq_det_add [CharP F 2] (w : OW F) :
    quadMinus 3 F b c w = (xM w).det + QN b c (nV w) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  have hs : ∑ i : Fin (3 - 1), w (Sum.inl i) * w (Sum.inr (Sum.inl i)) =
      w (Sum.inl idx0) * w (Sum.inr (Sum.inl idx0)) +
        w (Sum.inl idx1) * w (Sum.inr (Sum.inl idx1)) :=
    Fin.sum_univ_two (fun i : Fin 2 => w (Sum.inl i) * w (Sum.inr (Sum.inl i)))
  rw [hs]
  simp only [xM, nV, QN, Matrix.det_fin_two_of, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (w (Sum.inl idx1) * w (Sum.inr (Sum.inl idx1))) * h2

end CFSG.LocalAnalysis.RankThreeUC
