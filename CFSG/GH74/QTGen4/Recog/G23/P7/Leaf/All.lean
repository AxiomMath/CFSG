module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Main
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HR
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.LettersH
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HFacts
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTable
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.ZFitting
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.OneClass
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.Sylow2Cent
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.VertexCores
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.PbarMixed
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.FourClasses
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.Cor37
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.StepALocal
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.SuzukiCoherence
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.SuzukiIntegers
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.StepAArith
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27Abelian
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27Normalizer
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27Contradiction
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.GL3Facts
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.MStruct
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.Loc5
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.VertexLetters
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.TriClassify
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.TriLetters
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.TriCosetBound
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.TriNative
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.GhatInvolCent
public import CFSG.GH74.QTGen4.Recog.G23.NativeFactsB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

instance : G23Leaf LeafHR := ⟨leafHR⟩
instance : G23Leaf LeafSylow2Cent := ⟨leafSylow2Cent⟩
instance : G23Leaf LeafGL3Facts := ⟨leafGL3Facts⟩
instance : G23Leaf LeafVertexLetters := ⟨leafVertexLetters⟩
instance : G23Leaf LeafTriClassify := ⟨leafTriClassify⟩

theorem g23AtInv_holds : G23AtInvStmt :=
  g23AtInv_of_leaves leafLettersH leafHFacts leafHCharTable leafZFitting leafOneClass
    leafVertexCores leafPbarMixed leafFourClasses leafCor37 leafStepALocal leafSuzukiCoherence
    leafSuzukiIntegers leafStepAArith leafB27Abelian leafB27Normalizer leafB27Contradiction
    leafMStruct leafLoc5 leafTriLetters leafTriCosetBound leafTriNative leafGhatInvolCent
    ghat_simple ghat_card ghat_involutions_conj (fun e => lieModel_of_mulEquiv_native e)
    not_isSolvable_SL32

end CFSG.GH74.QTGen4.Recog.G23.P7
