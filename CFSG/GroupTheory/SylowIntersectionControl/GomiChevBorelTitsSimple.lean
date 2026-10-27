module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.LieType.BorelTits.CentralLift

public section

namespace CFSG.GroupTheory

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

theorem gomiChevBorelTits_of_simple
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → IsChevTwo K →
      CFSG.LieType.BorelTits.Holds K 2) : GomiChevBorelTits :=
  fun _ _ _ hL => CFSG.LieType.BorelTits.Holds.of_quotient_center hL.coprime_card_center
    (h _ hL.isSimpleGroup hL.isChevTwo)

end CFSG.GroupTheory
