module

public import CFSG.GH74.QTGen4.Recog.Ku.Main
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.IsMulCommutativeKuA
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.HInfCentralizerKuA
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.EqKuAOfElemAbelian
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.KuV2LeKuW
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.ExistsA6Model
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.ExistsIsParabolicL1
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.OTwoUpperInfL2
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.KuNEqL2DoubleCoset
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.ExistsY2TJ
public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.KuCloseHolds

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.H13

instance : KuLeaf LeafCardKuA := ⟨leafCardKuA⟩
instance : KuLeaf LeafIsMulCommutativeKuA := ⟨leafIsMulCommutativeKuA⟩
instance : KuLeaf LeafTInfCentralizerKuWLeKuA := ⟨leafTInfCentralizerKuWLeKuA⟩
instance : KuLeaf LeafHInfCentralizerKuA := ⟨leafHInfCentralizerKuA⟩
instance : KuLeaf LeafEqKuAOfElemAbelian := ⟨leafEqKuAOfElemAbelian⟩
instance : KuLeaf LeafKuV2LeKuW := ⟨leafKuV2LeKuW⟩
instance : KuLeaf LeafExistsA6Model := ⟨leafExistsA6Model⟩
instance : KuLeaf LeafExistsIsParabolicL1 := ⟨leafExistsIsParabolicL1⟩
instance : KuLeaf LeafOTwoUpperInfL2 := ⟨leafOTwoUpperInfL2⟩
instance : KuLeaf LeafCardOTwoUpperInfL2 := ⟨leafCardOTwoUpperInfL2⟩
instance : KuLeaf LeafKuNEqL2DoubleCoset := ⟨leafKuNEqL2DoubleCoset⟩
instance : KuLeaf LeafExistsY2TJ := ⟨leafExistsY2TJ⟩

theorem stmtKuM22_F4_holds :
    StmtKuM22_F4 :=
  stmtKuM22_F4_of_leaves leafCardKuA leafIsMulCommutativeKuA leafHInfCentralizerKuA
    leafEqKuAOfElemAbelian leafTInfCentralizerKuWLeKuA leafKuV2LeKuW leafExistsIsParabolicL1
    leafOTwoUpperInfL2 leafCardOTwoUpperInfL2 leafKuNEqL2DoubleCoset leafExistsA6Model
    leafKuCloseHolds

end CFSG.GH74.QTGen4.Ku
