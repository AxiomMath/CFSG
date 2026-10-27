module

public import CFSG.GH74.QTGen4.Recog.Ku.GenC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Inputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13


theorem stmtKuM22_of_leaves
    (hCard : LeafCardKuA) (hComm : LeafIsMulCommutativeKuA) (hHC : LeafHInfCentralizerKuA)
    (hEq : LeafEqKuAOfElemAbelian) (hTC : LeafTInfCentralizerKuWLeKuA) (hV2W : LeafKuV2LeKuW)
    (hPar : LeafExistsIsParabolicL1) (hL2 : LeafOTwoUpperInfL2) (hL2c : LeafCardOTwoUpperInfL2)
    (hDC : LeafKuNEqL2DoubleCoset) (hA6 : LeafExistsA6Model) (hClose : LeafKuCloseHolds) :
    StmtKuM22 := by
  haveI : KuLeaf LeafCardKuA := ⟨hCard⟩
  haveI : KuLeaf LeafIsMulCommutativeKuA := ⟨hComm⟩
  haveI : KuLeaf LeafHInfCentralizerKuA := ⟨hHC⟩
  haveI : KuLeaf LeafEqKuAOfElemAbelian := ⟨hEq⟩
  haveI : KuLeaf LeafTInfCentralizerKuWLeKuA := ⟨hTC⟩
  haveI : KuLeaf LeafKuV2LeKuW := ⟨hV2W⟩
  haveI : KuLeaf LeafExistsIsParabolicL1 := ⟨hPar⟩
  haveI : KuLeaf LeafOTwoUpperInfL2 := ⟨hL2⟩
  haveI : KuLeaf LeafCardOTwoUpperInfL2 := ⟨hL2c⟩
  haveI : KuLeaf LeafKuNEqL2DoubleCoset := ⟨hDC⟩
  rw [stmtKuM22_iff_of_hyp]
  intro G _ _ T M H P z hK
  obtain ⟨Ψ⟩ := hA6 hK
  exact hK.nonempty_mulEquiv_m22_of_close Ψ (hClose hK Ψ)

theorem stmtKuM22_F4_of_leaves
    (hCard : LeafCardKuA) (hComm : LeafIsMulCommutativeKuA) (hHC : LeafHInfCentralizerKuA)
    (hEq : LeafEqKuAOfElemAbelian) (hTC : LeafTInfCentralizerKuWLeKuA) (hV2W : LeafKuV2LeKuW)
    (hPar : LeafExistsIsParabolicL1) (hL2 : LeafOTwoUpperInfL2) (hL2c : LeafCardOTwoUpperInfL2)
    (hDC : LeafKuNEqL2DoubleCoset) (hA6 : LeafExistsA6Model) (hClose : LeafKuCloseHolds) :
    StmtKuM22_F4 := by
  intro G _ _ T M H P z hs hT hTM hTH h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  exact stmtKuM22_of_leaves hCard hComm hHC hEq hTC hV2W hPar hL2 hL2c hDC hA6 hClose G
    T M H P z hs hT hTM hTH h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

end CFSG.GH74.QTGen4.Ku
