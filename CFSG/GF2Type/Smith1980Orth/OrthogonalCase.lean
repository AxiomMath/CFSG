module

public import CFSG.GF2Type.Smith1980Orth.ReductionSix
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions

public section

namespace CFSG.GF2Type.Smith1980Orth

theorem orthogonalCase_of_six (h : Smith1980OrthogonalSixStatement) :
    CFSG.Yardstones.M3aba7dc4b8a8.OrthogonalCase := by
  intro G _ _ _ z hset hext w hcard h6 hev Mbar _ hMbar q hq hiso
  exact h G hset.1 z hset.2.2.2.2.1 hext w hcard h6 hev Mbar hMbar q hq hiso

end CFSG.GF2Type.Smith1980Orth
