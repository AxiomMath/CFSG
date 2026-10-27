module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Q8Target
public import CFSG.ClassicalInvolution.Q3.Q3T7FStar3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Proving

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.Q3T.MFS
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem fStarTwinSimpleLarge_of_memberFreeLarge (h : FStarTwinMemberFreeLarge) :
    CFSG.ClassicalInvolution.Q3.Thm7FStar3Large := by
  intro Y _ _ _ hnab hnot hBelow Ω K hΩ hK htrans hgen htwin
  obtain ⟨z, hzU⟩ := hΩ.classical K hK
  have hz : IsClassicalMember3 K z := hzU.toQ3 (by norm_num)
  have hgenK : Subgroup.normalClosure (K : Set Y) = ⊤ :=
    normalClosure_eq_top_of_transitive htrans hgen
  refine simpleGroup_of_le_fstar hgenK ?_
  by_cases hsup : genFittingFStar Y ⊔ K = ⊤
  · exact le_of_setting hBelow (setting_of_fstar hnab hz hgenK hsup)
      (fun hfree h3 => h Y hnab hBelow Ω K hΩ hK htrans hgen htwin hsup hfree h3 hnot)
  · exact le_fstar_of_sup_ne_top hnab hBelow hz hsup

end CFSG.ClassicalInvolution.Q3.PhilipHall.Proving
