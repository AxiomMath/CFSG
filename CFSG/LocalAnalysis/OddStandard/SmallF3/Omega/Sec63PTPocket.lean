module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec63PT_isI4PlusIn_top_of_equiv {A P : Type} [Group A] [Finite A] [Group P]
    (e : A ⧸ oddCore A ≃* P) {a : A} (ha : orderOf a = 2)
    (h : IsI4PlusIn (⊤ : Subgroup P) (e (QuotientGroup.mk a))) :
    IsI4PlusIn (⊤ : Subgroup A) a := by
  refine isI4PlusIn_top_of_quotient ha ?_
  have h' := isI4PlusIn_top_map_mulEquiv e.symm h
  rwa [MulEquiv.symm_apply_apply] at h'

end CFSG.OddStandard.SmallF3.Omega
