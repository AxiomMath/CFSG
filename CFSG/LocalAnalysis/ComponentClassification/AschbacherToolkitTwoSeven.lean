module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open
open AschbacherComponentAction AschbacherComponentInvolution

variable {G : Type} [Group G] [Finite G]

theorem even_card_center_quotient (L : Subgroup G) (hL : IsQuasisimple L) :
    Even (Nat.card (L ⧸ Subgroup.center L)) := by
  have : Group.IsPerfect L := ⟨hL.1⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  by_contra hodd
  have hsolv : Group.IsSolvable (L ⧸ Subgroup.center L) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
  exact Group.IsPerfect.not_isSolvable _ hsolv

end CFSG.ComponentClassification.AschbacherToolkit
