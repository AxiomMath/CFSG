module

public import CFSG.GH74.Uniqueness.SU.SU13TA3Loc
public import CFSG.GH74.Uniqueness.SU.SU13TB3GL

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup

theorem TA.L10.recog1 : TA.L10.Recog1 := by
  intro Λ _ _ hcard Q _ e x y hx3 hy2 hyx hxQ hy1
  exact GLR.nonempty_mulEquiv_GL23 Q hcard e x y hx3 hy2 hyx hxQ hy1

theorem loc10_of_isTwoAlt {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10) : Nonempty (Loc10 G z) :=
  loc10_of_isTwoAlt_of_recognition TA.L10.recog1 GLR.pPrimeCore_GL23 hz hH

end CFSG.GH74.Uniqueness.SU.SU13
