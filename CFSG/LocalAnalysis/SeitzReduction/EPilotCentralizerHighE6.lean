module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

theorem zero_ne_highNode_E6 : ((0 : Fin 6) : Fin (Tag.rank .E6)) ≠ highNode .E6 :=
  Fin.ne_of_val_ne (by decide)

theorem single_zero_mem_perpRoots_E6 :
    (Pi.single (0 : Fin 6) 1 : Fin (Tag.rank .E6) → ℤ) ∈ perpRoots .E6 :=
  single_mem_perpRoots zero_ne_highNode_E6

theorem e6Rep_zero_eq_pinnedElt :
    E6Pilot.e6Rep K 0 = pinnedElt .E6 (Pi.single (0 : Fin 6) 1) (1 : K) :=
  Subtype.ext E6Pilot.coe_e6Rep_zero

theorem highRootSL2_subgroupOf_le_rootPerpLevi_e6Rep_zero :
    (highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤
      rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) :=
  highRootSL2_subgroupOf_le_rootPerpLevi (Or.inl rfl) single_zero_mem_perpRoots_E6

theorem isTwoRadicalDecomp_e6Rep_zero [Finite K] [CharP K 2] :
    F4Pilot.IsTwoRadicalDecomp (E6Pilot.e6Rep K 0) (rootRadical .E6 K (Pi.single (0 : Fin 6) 1))
      (rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) := by
  rw [e6Rep_zero_eq_pinnedElt]
  exact isTwoRadicalDecomp_root (Or.inl rfl) (isRoot_single .E6 (0 : Fin 6)) one_ne_zero

end CFSG.SeitzReduction.EPilot
