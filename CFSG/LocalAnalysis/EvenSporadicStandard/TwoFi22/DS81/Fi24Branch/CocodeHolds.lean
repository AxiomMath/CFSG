module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeToData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.NoOffender

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem cocodeFacts_holds :
    CocodeFacts where
  noOffender := noOffender_holds
  exists_z := exists_z_holds
  data := fun G _ _ E t z hm hz => by
    letI := commGroupOfM24Out hm
    haveI := finite_E_of_m24Out hm
    obtain ⟨e, he, hez, het⟩ := exists_equiv_std hm hz
    refine CocodeX.toCocodeData hm hz (CocodeX.of_map e ?_)
    rw [he, hez, het]
    exact cocodeX_std

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
