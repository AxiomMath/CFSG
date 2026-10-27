module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverSmall
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalOfChar

public section

namespace CFSG.GroupTheory

open CFSG.QuasithinUnique.Bridge.Over

theorem chevParabolicRadicalSimple_of_mulEquiv_alt_six
    {K : Type} [Group K] [Finite K] (hK : IsSimpleGroup K) (e : K ≃* alternatingGroup (Fin 6)) :
    ChevParabolicRadicalSimple K :=
  chevParabolicRadicalSimple_of_overgroups hK (Overgroups.of_mulEquiv e.symm overgroups_alt_six)

end CFSG.GroupTheory
