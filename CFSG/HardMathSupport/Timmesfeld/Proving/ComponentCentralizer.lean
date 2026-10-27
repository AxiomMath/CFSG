module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

theorem isSubnormal_inf_right_aux {H K : Subgroup G} (h : IsSubnormal H K) (L : Subgroup G) :
    IsSubnormal (H ⊓ L) (K ⊓ L) :=
  h.inf L

theorem isComponentOf_inf_of_le {L K C : Subgroup G} (hL : IsComponentOf L K) (hLC : L ≤ C) :
    IsComponentOf L (K ⊓ C) := by
  obtain ⟨hLK, hsub, hq⟩ := hL
  refine ⟨le_inf hLK hLC, ?_, hq⟩
  have h := isSubnormal_inf_right_aux hsub C
  rwa [inf_eq_left.mpr hLC] at h

end CFSG.HardMathSupport.Timmesfeld.Proving

end
