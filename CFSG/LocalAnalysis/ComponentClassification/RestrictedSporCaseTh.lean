module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.ThSchreier
open CFSG.ComponentClassification.OuterAutomorphisms

theorem sporadicCase_Th : SporadicCase .Th := by
  refine sporadicCase_of_comps (fun G _ _ hG t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact compsSatisfy_of_charP
      ((ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G hG).1 t ht).1 _
  · have h : inner (NativeSporadic.Carrier .Th) = ⊤ := inner_Th
    rw [h]
    trivial

end CFSG.ComponentClassification.RestrictedStd.Spor
