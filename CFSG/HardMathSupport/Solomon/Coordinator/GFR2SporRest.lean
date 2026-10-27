module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporMat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporON
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

@[expose] def restNames : Finset TauCeti.SporadicName :=
  {.J3, .J4, .McL, .Suz, .He, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .HN, .Ly, .Th, .B, .M}

theorem sporNoPumpup_of_rest (hR : ∀ name ∈ restNames, SporNoPumpup name)
    (h12 : SporNoPumpup .M12) (h22 : SporNoPumpup .M22) :
    ∀ name ∈ sporResidualNames, SporNoPumpup name := by
  intro name hname
  by_cases hm : name ∈ restNames
  · exact hR name hm
  · have : name = .M12 ∨ name = .M22 := by
      revert hname hm
      cases name <;> simp [sporResidualNames, restNames]
    rcases this with rfl | rfl
    · exact h12
    · exact h22

section


theorem gapFinalPumpup_of_rest (hSpM : SporadicMultipliers) (hOrd : SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hR : ∀ name ∈ restNames, SporNoPumpup name) (hb : LieOrderBridge) (h1 : LieDownChev)
    (h2 : LieNoHatSix) : GapFinalPumpup :=
  gapFinalPumpup_of_residuals hSpM hOrd inputONGroup_holds
    (sporNoPumpup_of_rest hR (sporNoPumpup_M12 hSpM inputONGroup_holds hOut hbr)
      (sporNoPumpup_M22 hSpM inputONGroup_holds hOut hbr))
    onSimpleNoPumpup_holds hb h1 h2

end

end CFSG.HardMathSupport.Solomon.Coordinator
