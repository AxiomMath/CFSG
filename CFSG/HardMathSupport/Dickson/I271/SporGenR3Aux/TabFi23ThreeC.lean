
module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeCBase

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Twin
public import Certificates.Certificate17340

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
  CFSG.HardMathSupport.Dickson.I271.TabFi23C

section Main

theorem pConstrained_t3_two : PConstrainedShape 3 (Subgroup.centralizer ({t3 2} : Set CFSG.Sporadic.Fi23.J)) := by
  have h : fi23COK orb = true := Certificates.certificate17340
  have hT : Rep 31671 ((t3Tabs orb (chainLetters orb))[2]!) (t3 2) := rep_t3Tabs 2
  have hx : orderOf (t3 2) = 3 := t3_classData.2.2.1.1
  have hx3 : t3 2 * t3 2 * t3 2 = 1 := by
    have h1 := pow_orderOf_eq_one (t3 2)
    rwa [hx, pow_three'] at h1
  have h' : twinCheck orb (dTable orb) (genTables orb (-2)) ((t3Tabs orb (chainLetters orb))[2]!)
      4 = true := h
  obtain ⟨hK1, hK2, hK2b, hK3, hK4⟩ := twinCheck_spec hT h'
  exact pConstrained_of_twins ePt_smul hx3 thirdPt hK1 hK2 hK2b hK3 (cPt 4) (sep_cPt 4) hK4

end Main

end CFSG.HardMathSupport.Dickson.I271.TabFi23
