module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeNoComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.KGroupCarrier

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Proving

section Consumer


theorem isKGroup_gmat_of_carrier (hK : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) :
    CFSG.Open.IsKGroup CFSG.Monster.Generated.Gmat := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* NativeSporadic.Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  let eG : NativeSporadic.Carrier .M ≃* CFSG.Monster.Generated.Gmat := e.symm.trans φ
  exact hK.of_surjective eG.toMonoidHom eG.surjective

theorem sporPair_M_three_of_kGroupNoComp (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 3) (hChev : ChevStrong 3)
    (hFi24 : SporStrong .Fi24Prime 3) (hTh : SporStrong .Th 3)
    (hA : CentThreeA (NativeSporadic.Carrier .M))
    (hB : CFSG.Open.IsKGroup CFSG.Monster.Generated.Gmat → M3ResBNoComp)
    (hC : CentThreeC (NativeSporadic.Carrier .M)) : SporPair .M 3 := by
  intro X _ _ hX K B hH hN hS hF hO'
  exact sporPair_M_three_of_tab' hOut hSpM hBr hP hChev hFi24 hTh hA
    (hB (isKGroup_gmat_of_carrier (isKGroup_carrier_of_sporType hBr hX hS))) hC
    X hX K B hH hN hS hF hO'

end Consumer

end CFSG.HardMathSupport.Dickson.I271
