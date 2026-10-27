module

public import CFSG.ClassicalInvolution.Q3.TL4D4NC
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem d4OddAutInnerNC3_proved : D4OddAutInnerNC3 :=
  fun X _ _ hX hZ f hf hker s hs _ α hα hfix =>
    d4OddAutInner3_all X hX hZ f hf hker s hs α hα hfix

end CFSG.ClassicalInvolution.Q3.TL4
