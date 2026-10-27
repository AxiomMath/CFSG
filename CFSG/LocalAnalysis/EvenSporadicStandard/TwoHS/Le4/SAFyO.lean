module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyLy
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUOProps

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem sect8InputO_of_ly (hQ : Q0Facts) (hLy : Sect8InputLy) (hK : KNotInLf hQ)
    (hCl : Cl16OfClass hQ) : Sect8InputO hQ := by
  intro G _ _ L f s y S₀ n hH C hC T K hT w hwT hwE hwc hwy hwg
  have hff : f ^ 2 * f ^ 2 = 1 := by
    rw [← pow_add]; exact hH.f_pow_four
  have hw : w * f ^ 2 = f ^ 2 * w := hwc (f ^ 2) (pow_mem hC.f_mem 2) hff
  have hwf := hK G L f s y S₀ n hH C hC T K hT w hwT hwE hwc hwy hwg
  exact hCl G L f s y S₀ n hH C hC T K hT w hwT hwE hwc hwy (hLy G L f s y S₀ n hH w hw hwf hwg)

end CFSG.EvenSporadicStandard.TwoHS
