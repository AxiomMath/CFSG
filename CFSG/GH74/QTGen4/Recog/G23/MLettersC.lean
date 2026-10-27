module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public meta import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.GH74.QTGen4.Recog.G23

theorem GL3_two_transitive :
    ∀ x x' : Fin 3 → ZMod 2, x ≠ 0 → x' ≠ 0 →
      ∃ B : Fin 3 → Fin 3 → ZMod 2,
        (Matrix.of B).det ≠ 0 ∧ Matrix.mulVec (Matrix.of B) x = x' := by
  decide +kernel

end CFSG.GH74.QTGen4.Recog.G23
