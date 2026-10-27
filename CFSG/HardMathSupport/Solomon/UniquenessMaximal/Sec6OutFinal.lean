module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Final
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3
public import CFSG.HardMathSupport.Solomon.Coordinator.ONGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylowUM
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input254
public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaGen
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VExt
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Solomon.Coordinator.I713
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Top

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem sec6Out_final
   
    (hSF : SignalizerFunctorTheoremK) (h21 : Prop21) (h24 : Lemma24) (h31 : Lemma31)
    (h514 : Lemma514) (h515 : Lemma515)
    (T112 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (TL2 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableL2)
    (F254 : GenL3.Input25_4FactsNarrow) : Sec6Out :=
  sec6Out_of_inputs hSF CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge h21
      (alphaGenHypAll_of_i713 i_7_13_1_pPrime_holds) h24 h31 h514 h515 Proving.inputL34Cover_holds
      inputONGroup_holds (input11_2Ext_of_tables T112 TL2 tables112Types_holds tables112More_holds)
      input18_3_4_holds inputOutON_of_hatON inputSylowON_holds_of_hatON
      (input23_25_2_of_facts inputOutON_of_hatON inputSylowON_holds_of_hatON input23_25_2Facts_holds)
      input18_3_12_holds (GenL3.input25_4_of_narrow F254)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
