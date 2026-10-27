module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.L5U5.ModelsBasic

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

@[expose] def H4 (M : ModelData F) : Subgroup (GL (Fin 2) F) where
  carrier := {g | g ∈ M.U2 ∧ (Matrix.GeneralLinearGroup.det g) ^ 4 = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.U2.mul_mem ha hb, ?_⟩
    rw [map_mul, mul_pow, ha', hb', one_mul]
  one_mem' := ⟨M.U2.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.U2.inv_mem ha, ?_⟩
    rw [map_inv, inv_pow, ha', inv_one]

theorem mem_H4 {M : ModelData F} {g : GL (Fin 2) F} :
    g ∈ H4 M ↔ g ∈ M.U2 ∧ (Matrix.GeneralLinearGroup.det g) ^ 4 = 1 := Iff.rfl

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
