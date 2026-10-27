module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GorensteinWalter

theorem toPGL_surjective_of_charTwo' (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Function.Surjective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) := by
  intro x
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  have : Fintype K := Fintype.ofFinite K
  exact (pgl2_mk_mem_psl2_range_iff_det_isSquare A).2
    (FiniteField.isSquare_of_char_two (ringChar.eq K 2) _)

end CFSG.GorensteinWalter
