module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Lie
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29HS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Sporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmall
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

theorem onanNoSL29N_holds :
    ONanNoSL29N := by
  intro N _ _ h K _ _ hK hZ hA f hf
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact noSL29_of_lieModel_psu_three_five h K hK hZ hA f hf
  · exact noSL29_of_lieModel_psl_three_seven h K hK hZ hA f hf
  · exact noSL29_of_isSporadic_m22 h K hK hZ hA f hf
  · exact noSL29_of_isSporadic_m23 h K hK hZ hA f hf
  · exact noSL29_of_isSporadic_m24 h K hK hZ hA f hf
  · exact noSL29_of_isSporadic_hs h K hK hZ hA f hf
  · exact noSL29_of_isSporadic_ru h K hK hZ hA f hf
  · exact noSL29_of_lieModel_psl_five_two h K hK hZ hA f hf
  · exact noSL29_of_isSporadic_j2 h K hK hZ hA f hf
  · exact noSL29_of_lieModel_psp_two_two_two h K hK hZ hA f hf

theorem onanNoSL29Y_holds :
    PartA.ONanNoSL29Y :=
  onanNoSL29Y_of_facts onanNoSL29N_holds onanOutSmall_holds onanCenterFree_holds

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
