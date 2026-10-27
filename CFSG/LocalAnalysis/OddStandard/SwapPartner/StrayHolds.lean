module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayMain
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem dihedralOuterInvolutionFact_holds :
    DihedralOuterInvolutionFact :=
  CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.dihedral_outer_involution_holds

theorem hStray_of_swapShape_holds
    {X : Type} [Group X] [Finite X] {t : X} {Sg V : Subgroup X}
    (h : SwapShape t Sg V) :
    ∀ J : Subgroup X, CFSG.IsComponent J → ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥ → t ∈ J :=
  hStray_of_swapShape dihedralOuterInvolutionFact_holds h

end CFSG.OddStandard.AltStdSec.SwapPartner
