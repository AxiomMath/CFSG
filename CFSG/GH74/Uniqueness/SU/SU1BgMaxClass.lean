module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Bg.TwoGroups.Basic
public import CFSG.GH74.Uniqueness.SU.SU1MaxClass

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

theorem b_maximalClass_of_small_centralizer :
    CFSG.GH74.GLS.Bg.B_maximalClass_of_small_centralizer := by
  intro p hp P _ _ hP hcard x hx
  exact maximalClass_aux CFSG.GH74.GLS.Bg.TwoGroups.ig_9_16 p hp (Nat.card P) P rfl hP hcard x hx

theorem ig10_24 : CFSG.GH74.GLS.Bg.B_maximalClass_of_small_centralizer :=
  b_maximalClass_of_small_centralizer

end CFSG.GH74.Uniqueness.SU.SU1
