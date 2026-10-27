module

public import CFSG.HardMathSupport.Solomon.Proving.Fi22AutTables
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

structure I271FamiliesRest : Prop where
  nnHatSixRank : I271NNHatSixRank
  autBalanceSix : I271AutBalanceAltSix
  nnOther : I271NNOther
  altDiv : I271AltDiv
  altNdiv : I271AltNdiv
  chevPBal : I271ChevPBal
  chevPExc : I271ChevPExc
  sporGen : I271SporGen
  autBalanceON : I271AutBalanceON
  onLow : I271ONLow
  chevQL34 : I271ChevQLThreeFour
  chevQ : I271ChevQ


theorem fi22Catalogue_isSimpleGroup :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := by
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) :=
    CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  exact (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi22).some.symm.isSimpleGroup

theorem i271Fi22Aut_holds : I271Fi22Aut :=
  CFSG.HardMathSupport.Solomon.Proving.i271Fi22Aut_of_tables
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds sporadicOrdersTable_holds
    fi22Catalogue_isSimpleGroup

theorem input27_1K_of_familiesRest (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (hF : I271FamiliesRest) : Input27_1K :=
  input27_1K_of_families T TL TT
    { nnHatSixRank := hF.nnHatSixRank
      autBalanceSix := hF.autBalanceSix
      nnOther := hF.nnOther
      altDiv := hF.altDiv
      altNdiv := hF.altNdiv
      chevPBal := hF.chevPBal
      chevPExc := hF.chevPExc
      sporGen := hF.sporGen
      fi22Aut := i271Fi22Aut_holds
      autBalanceON := hF.autBalanceON
      onLow := hF.onLow
      chevQL34 := hF.chevQL34
      chevQ := hF.chevQ }

end CFSG.HardMathSupport.Solomon.Coordinator
