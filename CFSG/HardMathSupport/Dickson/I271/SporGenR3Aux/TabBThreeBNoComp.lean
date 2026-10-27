module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeBChain
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeBLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.KGroupCarrier

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.CatLeaf

theorem B3BLeaf.card_B_eq_orderBabyMonster (hBr : SporadicBridges)
    (hOrd : SporadicOrdersTable) : Nat.card NativeSporadic.B = orderBabyMonster := by
  obtain ⟨e⟩ := hBr .B
  exact (Nat.card_congr e.toEquiv).trans (hOrd .B)

theorem b3BComponentLeaf_of_catalogue (hGA : GriessAllModelsStatement)
    (hLO : LieOrderFormulasInput) (hBA : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    (hSpM : SporadicMultipliers) (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable)
    (hBr : SporadicBridges) (hX : CFSG.Open.IsKGroup NativeSporadic.B) : B3BComponentLeaf := by
  intro J hq h3 h7 haut
  have hcard := B3BLeaf.card_B_eq_orderBabyMonster hBr hOrd
  haveI : Finite NativeSporadic.B :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; unfold orderBabyMonster; norm_num)
  exact B3BLeaf.b3b_leaf_catalogue hGA hLO hBA hSpM hOut hOrd hq (hX.subgroup J) h3 h7
    (by rw [← hcard]; exact Subgroup.card_subgroup_dvd_card J) haut

section NoComp

set_option linter.unusedSectionVars false


theorem tabBThreeBNoComp_of_kGroup
    (hGA : GriessAllModelsStatement)
    (hLO : LieOrderFormulasInput) (hBA : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    (hSpM : SporadicMultipliers) (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable)
    (hBr : SporadicBridges) (hX : CFSG.Open.IsKGroup NativeSporadic.B) : TabBThreeBNoComp :=
  b3b_noComp_of_leaf (b3BComponentLeaf_of_catalogue hGA hLO hBA hSpM hOut hOrd hBr hX)

end NoComp

section Consumer

set_option linter.unusedSectionVars false


theorem sporPair_B_three_of_tab' (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .B 3) (hChev : ChevStrong 3)
    (hFi22 : SporStrong .Fi22 3) (hA : TabBThreeACard)
    (hB : CFSG.Open.IsKGroup NativeSporadic.B → TabBThreeBNoComp) : SporPair .B 3 := by
  intro X _ _ hX K B hH hN hS hF hO
  exact sporPair_B_three_of_tab hOut hSpM hBr hP hChev hFi22 hA
    (hB (isKGroup_carrier_of_sporType hBr hX hS)) X hX K B hH hN hS hF hO

end Consumer

end CFSG.HardMathSupport.Dickson.I271
