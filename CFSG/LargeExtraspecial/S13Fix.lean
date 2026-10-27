module

public import CFSG.LargeExtraspecial.S13Lin
public import CFSG.LargeExtraspecial.S4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem finrank_fixSub_Lbar {g : G} (H : Hyp4 S g) :
    finrank (ZMod 2) (fixSub S (S.Lbar g)) = 1 := by
  rw [H.fixSub_eq]
  exact finrank_span_singleton (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)

end CFSG.LargeExtraspecial.S13
