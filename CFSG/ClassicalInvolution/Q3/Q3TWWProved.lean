module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollCert
public import CFSG.ClassicalInvolution.Q3.Q3TWWAdjB
public import CFSG.ClassicalInvolution.Q3.Q3WChain
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjMain
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.WeakCT.SpinOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameDLSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSp4Levi
public import CFSG.ClassicalInvolution.Q3.Q3TWInputs
public import CFSG.ClassicalInvolution.Q3.Q3TWCollB
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinusMap
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.RouteD.TypeCRecognition
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDRecognition

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

theorem weakCT3MinusMap_proved :
    ∀ N : ℕ, 6 ≤ N → WeakCT3MinusMap N :=
  fun _ hN => weakCT3MinusMap_of_collapse td4Collapse_proved (by omega)

end CFSG.ClassicalInvolution.Q3.Q3TW
