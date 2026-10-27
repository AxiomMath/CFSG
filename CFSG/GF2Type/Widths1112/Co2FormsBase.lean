
module

public import CFSG.GF2Type.Widths1112.Co2FormDefs
public import CFSG.GF2Type.Widths1112.Spin

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native
  CFSG.GF2W1112 Matrix

private theorem dot_transpose_mulVec (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (u v : Vec22) :
    u ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
  rw [dotProduct_mulVec u Mᵀ v, Matrix.vecMul_transpose M u]
  exact dotProduct_comm _ _

private theorem dot_mulVec_eq_transpose (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (u v : Vec22) :
    u ⬝ᵥ (M *ᵥ v) = (Mᵀ *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec u M v, Matrix.mulVec_transpose M u]

private theorem bil₀₂_eq_Q (u v : Vec22) :
    bil₀₂ u v = u ⬝ᵥ (Qm22 *ᵥ v) + v ⬝ᵥ (Qm22 *ᵥ u) := by
  unfold bil₀₂
  rw [Matrix.add_mulVec, dotProduct_add, dot_transpose_mulVec]

theorem bil₀₂_eq_F (u v : Vec22) : bil₀₂ u v = ((Qm22 + Qm22ᵀ) *ᵥ u) ⬝ᵥ v := by
  unfold bil₀₂
  rw [dot_mulVec_eq_transpose, Matrix.transpose_add, Matrix.transpose_transpose,
    add_comm Qm22ᵀ Qm22]

private theorem rowsMatrix_w12AddRows22 (X Y : Array ℕ) :
    rowsMatrix 22 (w12AddRows22 X Y) = rowsMatrix 22 X + rowsMatrix 22 Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold w12AddRows22
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor]
  rfl

theorem co2F0_eq : Qm22 + Qm22ᵀ = rowsMatrix 22 (w12Co2F0Rows ()) := by
  unfold Qm22 w12Co2F0Rows
  rw [rowsMatrix_w12AddRows22, rowsMatrix_transposeRows]

theorem polar_q₀₂ (u v : Vec22) : q₀₂ (u + v) - q₀₂ u - q₀₂ v = bil₀₂ u v := by
  rw [bil₀₂_eq_Q]
  unfold q₀₂
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  ring

theorem bil₀₂_comm (u v : Vec22) : bil₀₂ u v = bil₀₂ v u := by
  rw [bil₀₂_eq_Q, bil₀₂_eq_Q, add_comm]

theorem bil₀₂_add_left (u u' v : Vec22) : bil₀₂ (u + u') v = bil₀₂ u v + bil₀₂ u' v := by
  unfold bil₀₂
  rw [add_dotProduct]

theorem q₀₂_toVecD (x : ℕ) :
    q₀₂ (toVecD 22 x) = if w12QN 22 (w12Co2QT ()) x = true then 1 else 0 := by
  unfold q₀₂ Qm22
  exact w12QN_spec 22 w12Co2QRows x

theorem bil₀₂_toVecD (u v : ℕ) :
    bil₀₂ (toVecD 22 u) (toVecD 22 v) =
      if w12BN 22 (w12Co2FT ()) u v = true then 1 else 0 := by
  unfold bil₀₂
  rw [co2F0_eq]
  exact w12BN_spec 22 (w12Co2F0Rows ()) u v

end CFSG.GF2Type.Widths1112
