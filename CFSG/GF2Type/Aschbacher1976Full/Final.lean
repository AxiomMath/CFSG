module

public import CFSG.GF2Type.Aschbacher1976Full.Reduction
public import CFSG.GF2Type.Aschbacher1976Full.Shape
public import CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution
public import CFSG.GF2Type.Aschbacher1976Full.LeafDihedral
public import CFSG.GF2Type.Aschbacher1976Full.LeafSemidihedral
public import CFSG.GF2Type.Aschbacher1976Full.LeafQ8
public import CFSG.GF2Type.Aschbacher1976Full.LeafBigCenter
public import CFSG.GF2Type.Aschbacher1976Full.WidthConfig
public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8
public import CFSG.GF2Type.Aschbacher1976Full.HSLeafBad
public import CFSG.GF2Type.Aschbacher1976Full.HSBadReduction
public import CFSG.GroupTheory.TransferOrderFour
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxAssembly
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxSix
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxNine2
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxPLocal
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxFrattini
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxFinW
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxQuad
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxL5

public section

namespace CFSG.GF2Type.Aschbacher1976Full

theorem HS.badCruxStmt_holds : HS.BadCruxStmt :=
  HS.badCruxStmt_of_inputs HS.cruxSix_holds HS.cruxNine_holds HS.cruxPLocal_holds
    HS.cruxFrattini_holds HS.cruxFinW_holds (HS.cruxQuad_holds) HS.cruxL5_holds

theorem aschbacher1976Statement_holds
    : Aschbacher1976Statement :=
  aschbacher1976Statement_of_inputs
    { shape := asc76ShapeHolds
      dihedral := leafDihedral_holds
      semidihedral := leafSemidihedral_holds
      q8 := leafQ8_holds
      uniqueInvolution := leafUniqueInvolution_holds
      bigCenter := leafBigCenter_holds
      widthGeThree := Width.leafWidthGeThree_holds
      z4q8 := leafZ4Q8_holds
      z4q8sq := HS.leafZ4Q8Sq_of_bad
        (HS.hsPartBad_of_crux CFSG.GroupTheory.TransferOrderFour.transferCoreStmt_holds
          HS.badCruxStmt_holds) }

end CFSG.GF2Type.Aschbacher1976Full
