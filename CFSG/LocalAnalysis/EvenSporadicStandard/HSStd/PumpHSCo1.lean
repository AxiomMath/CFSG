module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0ClsK

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem co1InvCentralizers_proved :
    Co1InvCentralizers := by
  intro Y _ _ hY y hy h
  rcases TwoCo1.card_centralizer_involution_of_isSporadic_co1 hY hy with h1 | h1 | h1 <;>
    omega

end CFSG.EvenSporadicStandard.HSStd.PumpHS
