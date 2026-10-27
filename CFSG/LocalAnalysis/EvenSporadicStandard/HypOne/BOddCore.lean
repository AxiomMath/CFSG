module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.Monster.B.CTIB.OddCoreFree
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic



theorem oddCore_centralizer_B {X : NativeSporadic.B} (hX : orderOf X = 2) :
    CFSG.Assembly.oddCore (centralizer ({X} : Set NativeSporadic.B)) = ⊥ := by
  have hS := (CFSG.Monster.B.CTIB.native_B_all_involution_centralizers_odd_core_free).1
  have h1 : orderOf (CFSG.Monster.B.CTIB.iotaEquiv X) = 2 :=
    (@MulEquiv.orderOf_eq _ Units.instMonoid _ _ CFSG.Monster.B.CTIB.iotaEquiv X).trans hX
  have h2 := hS _ h1
  have e := (@CFSG.Monster.B.CTIB.centralizerEquiv NativeSporadic.B CFSG.Monster.B.Sbp
    Units.instGroup _ CFSG.Monster.B.CTIB.iotaEquiv X).symm
  exact CFSG.Monster.B.CTIB.oddCore_eq_bot_of_equiv e h2

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
