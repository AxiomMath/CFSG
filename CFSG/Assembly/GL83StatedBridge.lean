module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Assembly

open CFSG.Open

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem largeEvenScalars_eq_statedScalars : LargeEvenScalars ι K = StatedScalars ι K := rfl

theorem largeEvenProj_eq_statedProj (H : Subgroup (GL ι K)) :
    LargeEvenProj H = StatedProj H := rfl

theorem largeEvenSUGroup_eq_statedSU (n q : ℕ) :
    LargeEvenSUGroup (Fin n) K q = StatedSU n q K := rfl

theorem largeEvenSpGroup_eq_statedSp (m : ℕ) : LargeEvenSpGroup K m = StatedSp m K := rfl

theorem largeEvenOmega_eq_statedOmega (Q : (ι → K) → K) : LargeEvenOmega Q = StatedOmega Q := rfl

theorem largeEvenSLGroup_eq_statedSL (n : ℕ) : LargeEvenSLGroup (Fin n) K = StatedSL n K :=
  (StatedAPI.statedSL_eq_ker_det n K).symm

end CFSG.Assembly
