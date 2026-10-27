module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinFam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoFam

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.HardMathSupport.Timmesfeld.DefChar

theorem crossCharTwoFamCat_A (hHeis : LinHeisenbergBalance) : CrossCharTwoFamCat .A := by
  refine crossCharTwoFamCat_of_at regimeAThree (crossCharTwoFamAt_A_ge_two hHeis) ?_
  rintro idx hk p hp hp5 hc hR hnexc
  obtain ⟨m, q, hmq⟩ := hk
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 idx.2).1
  rw [hmq] at hrange
  have hm1 : m = 1 := by
    by_contra h
    exact hR ⟨m, q, hmq, by have := hrange.1; omega⟩
  subst hm1
  exact crossCharTwoFamAt_A_one idx ⟨1, q, hmq⟩ p hp hp5 hc ⟨q, hmq⟩ hnexc

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
