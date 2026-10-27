module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNeg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniSig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrth

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.Y10GField

theorem i14NegPieceC_of (hRig : GGLabelRigidInput) (hFldSymp : FldSymp) (hFldOrth : FldOrth) :
    I14NegPieceC := by
  intro S _ _ p α J labK labJ hp hp2 hcen hlabK hlabJ hα hJ hK5
  obtain ⟨hKt, hKr⟩ := hK5
  rcases hKt with h | h | h
  · exact Y10GNegBC.negC_orth hRig hFldOrth hp hp2 hcen ⟨h, hKr⟩ hlabK hα hlabJ hJ
  · exact Y10GNegBC.negC_symp hRig hFldSymp hp hp2 hcen (Or.inl h) hlabK hα hlabJ hJ
  · exact Y10GNegBC.negC_symp hRig hFldSymp hp hp2 hcen (Or.inr h) hlabK hα hlabJ hJ

section Certificates


theorem i14NegPieceB_holds : I14NegPieceB :=
  Y10GNegBC.i14NegPieceB_of ggLabelRigidInput_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniSig.fldUni_holds

theorem i14NegPieceC_holds : I14NegPieceC :=
  i14NegPieceC_of ggLabelRigidInput_holds Y10GField.fldSymp_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth.fldOrth_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10F
