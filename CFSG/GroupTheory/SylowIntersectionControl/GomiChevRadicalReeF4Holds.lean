module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Exceptional
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalOfChar

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint

theorem chevParabolicRadicalSimple_of_lieModel_twistedF4
    {K : Type} [Group K] [Finite K] {n f : ℕ} (hK : IsSimpleGroup K)
    (h : LieModel K .twistedF4 n 2 f) : ChevParabolicRadicalSimple K :=
  chevParabolicRadicalSimple_of_overgroups hK
    (Quasithin.LieOver.asLieTwoAt_twistedF4 n f K hK h.admissible h).1

end CFSG.GroupTheory
