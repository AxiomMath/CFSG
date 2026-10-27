module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Red
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Rows
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11J3
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Suz
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.ComponentClassification.GSThmB

theorem cf81Exit11Recognition_holds
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hSuzO : SolMax.SuzOuterComponentsInput)
    (h3 : CF81X11CharThree) (hU52 : CF81X11U52) (hON : CF81X11ON) : CF81Exit11Recognition :=
  cf81Exit11Recognition_of_recognition
    (X11.recognition_of_rows hGLS CatLeafProof.lieOrderFormulasInput h3 hU52 hON
      (fun _ _ _ _ h _ hn => h.not_alt hn) (fun _ _ _ _ h => h.not_j3)
      (fun _ _ _ _ h => h.not_suz hSuzO))

end CFSG.ComponentClassification.GSThmB
