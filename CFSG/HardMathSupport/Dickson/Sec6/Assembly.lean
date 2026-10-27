module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Alt
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.D44Centre
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Glue
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Reduction
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Final
public import CFSG.HardMathSupport.Dickson.Sec6.I923Final
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Assembly
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMNo65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.MNo186
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Final
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporMonsterSection
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestB

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.M67c2c3e09a6b


theorem sec6Out_of_remaining
    (hSpor : Up34SporLeaf) (hChev2 : Up34Chev2Leaf)
    (h09 : CFSG.Yardstones.M67c2c3e09a6b.I271OpenFamilies) (hM65 : I1431.NoOrder 65 NativeSporadic.M)
    (hTh93 : I1431.NoOrder 93 NativeSporadic.Th) (h6 : I1431.I1431LieRest)
    (hR : I1431.D4RootSL2) : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Out :=
  have h03 := CFSG.HardMathSupport.Dickson.LocalTwoBalance.localTwoBalanceThreeFive_parts
  sec6Out_of_open_residuals ⟨h03.1, h03.2.1, h03.2.2.1, h03.2.2.2⟩
    CFSG.HardMathSupport.Timmesfeld.Coordinator.localTwoBalanceSimpleGtFive_holds
    ⟨j4ThreeCentralizerResidual CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group,
      b3SporRestPairs_of (b3SporPair_B_seven CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
        CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds)⟩
    h09 (up34Statement_of_core
        (up34Core_of_leaves up34AltLeaf_holds hSpor up34OddLeaf_holds hChev2 up34D44Centre_holds
            up34L364NotInnDiag_holds)) gen3D4_holds
    I923.y923LieRest_holds (I1431.input14_31_4_of_rest
        (I1431.i1431SporRest_of_open I1431.noOrder65_B hM65 (I1431.noOrder186_B_of_table
            CFSG.Monster.Existence.babyTableIII)
            (I1431.noOrder186_M_of_noOrder93_Th hTh93)) h6 (I1431.i1431D4Rest_of_rootSL2 hR))

end CFSG.HardMathSupport.Dickson.Sec6
