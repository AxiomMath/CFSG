module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Equiv Equiv.Perm CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

section Facts4

variable (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10)

include h7 h10

theorem Sfun_cent0 (x : UT3 F4c)
    (h1 : Sfun m x * ub m = ub m * Sfun m x) (h2 : Sfun m x * vb m = vb m * Sfun m x)
    (h3 : Sfun m x * xb1 m = xb1 m * Sfun m x) (h4 : Sfun m x * xb2 m = xb2 m * Sfun m x) :
    Sfun m x = 1 ∨ Sfun m x = tb m := by
  revert x
  interval_cases m <;> decide +kernel

theorem Sfun_cent1 (x : UT3 F4c)
    (h1 : (Sfun m x * c3 m) * ub m = ub m * (Sfun m x * c3 m))
    (h2 : (Sfun m x * c3 m) * vb m = vb m * (Sfun m x * c3 m))
    (h3 : (Sfun m x * c3 m) * xb1 m = xb1 m * (Sfun m x * c3 m))
    (h4 : (Sfun m x * c3 m) * xb2 m = xb2 m * (Sfun m x * c3 m)) : False := by
  revert x
  interval_cases m <;> decide +kernel

theorem Sfun_cent2 (x : UT3 F4c)
    (h1 : (Sfun m x * (c3 m * c3 m)) * ub m = ub m * (Sfun m x * (c3 m * c3 m)))
    (h2 : (Sfun m x * (c3 m * c3 m)) * vb m = vb m * (Sfun m x * (c3 m * c3 m)))
    (h3 : (Sfun m x * (c3 m * c3 m)) * xb1 m = xb1 m * (Sfun m x * (c3 m * c3 m)))
    (h4 : (Sfun m x * (c3 m * c3 m)) * xb2 m = xb2 m * (Sfun m x * (c3 m * c3 m))) : False := by
  revert x
  interval_cases m <;> decide +kernel

end Facts4

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
