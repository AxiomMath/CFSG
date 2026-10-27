module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

@[expose, reducible] def glVecAction : MulAction (GL n R) (n → R) where
  smul g v := Matrix.mulVec (g : Matrix n n R) v
  one_smul v := by
    show Matrix.mulVec ((1 : GL n R) : Matrix n n R) v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show Matrix.mulVec ((g * h : GL n R) : Matrix n n R) v =
      Matrix.mulVec (g : Matrix n n R) (Matrix.mulVec (h : Matrix n n R) v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

end CFSG.EvenSporadicStandard.Induction.AutBound
