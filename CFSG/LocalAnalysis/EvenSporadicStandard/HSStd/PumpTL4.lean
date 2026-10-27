module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTL4Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKillType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterAltStd

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem l4CentralTwoTrivial_proved : L4CentralTwoTrivial := by
  intro K _ _ hK hK2 i hi hm
  have hf : 2 ≤ 2 ^ i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  exact center_eq_bot_of_psl_four hK hK2 hf hm

end CFSG.EvenSporadicStandard.HSStd.PumpT
