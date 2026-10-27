module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcG2F4
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcTwistedE6
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcTriality
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ree
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.NonA

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Cooperstein.Coordinator TauCeti


theorem gf2NoFFLieOddExceptional : GF2NoFFLieOddExceptional := by
  intro d hd hchar _
  rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, h3, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ |
    ⟨m, hq⟩
  · exact noFFModule_lie_E6 d hq (by rw [hq] at hchar; simpa using hchar)
  · exact noFFModule_lie_E7 d hq (by rw [hq] at hchar; simpa using hchar)
  · exact noFFModule_lie_E8 d hq (by rw [hq] at hchar; simpa using hchar)
  · exact noFFModule_lie_F4 d hq (by rw [hq] at hchar; simpa using hchar)
  · exact noFFModule_lie_G2 d hq (by rw [hq] at hchar; simpa using hchar) h3
  · exact noFFModule_lie_twistedE6 d hq (by rw [hq] at hchar; simpa using hchar)
  · exact noFFModule_lie_trialityD4 d hq (by rw [hq] at hchar; simpa using hchar)
  · exact noFFModule_lie_reeG2 d hq

theorem gf2NoFFLieOdd_of_small (hSm : GF2NoFFLieOddSmall) :
    GF2NoFFLieOdd :=
  gf2NoFFLieOdd_of_nodes gf2NoFFLieOddExceptional hSm

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
