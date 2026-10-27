module

public import CFSG.GH74.Uniqueness.SU.SU13Main9
public import CFSG.GH74.Uniqueness.SU.KI7dMain
public import CFSG.GH74.Uniqueness.SU.KI8C
public import CFSG.GH74.Uniqueness.SU.SU13Bridge

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

theorem thm231_of_ki8bc (hKI8b : K.KI8b) (hKI8c : K.KI8c) : Thm231Stmt :=
  thm231_of_ki7d_ki8bc K.ki7d hKI8b hKI8c

theorem s_noTwoAnNineTen_of_ki8bc (hKI8b : K.KI8b) (hKI8c : K.KI8c) :
    CFSG.GH74.GLS.Stage12.S_noTwoAnNineTen :=
  s_noTwoAnNineTen_of_thm231 (thm231_of_ki8bc hKI8b hKI8c)

theorem thm231_of_ki8c
    (hKI8c : K.KI8c) : Thm231Stmt :=
  thm231_of_ki8bc K.ki8b hKI8c

theorem thm231 :
    Thm231Stmt :=
  thm231_of_ki8bc K.ki8b K.ki8c

end CFSG.GH74.Uniqueness.SU.SU13
