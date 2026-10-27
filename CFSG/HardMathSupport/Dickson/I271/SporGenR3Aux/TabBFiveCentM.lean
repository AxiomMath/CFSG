module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentRes
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCentA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Native


theorem centFiveA_MGriess_res (hR : BFiveCentRes) (hCo : Co1FiveInputs) :
    CentFiveA MGriess := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  exact centFiveA_of_bounds' hE
    (fun t k ht htc hk htk _ hL hLc =>
      card_inf_centralizer_le_of_twoA_res hE tabBFive_hconj hR ht htc hk htk hL hLc)
    (h2B_MGriess (co1FiveBound_of_inputs hCo) hE card_nativeB) (hG5_MGriess hE)

theorem centFiveA_M_res (hR : BFiveCentRes) (hCo : Co1FiveInputs) :
    CentFiveA (NativeSporadic.Carrier .M) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : MGriess ≃* NativeSporadic.Carrier .M := e₀
  exact CentFiveA.of_equiv e.symm (centFiveA_MGriess_res hR hCo)

end Native

end CFSG.HardMathSupport.Dickson.I271.TabMFive
