module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Fusion1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Cube
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.A8Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Fusion2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Fusion3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.A8Pictures
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.GzOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.GzClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Y4a
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Gz9
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.StructX
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.TableIII
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Parity
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.TableIV
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Perp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.TableV
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.S7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.SixA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.TableVI
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.OddInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.FiveCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Step.Order
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Segev28Proof

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem f5Local_of_isF5Type_of_inputs (hI : TwoHSInterface) (hS : SuborbitFacts)
    (hC : CSideFacts) (hM : M11Facts) (hU : U35Facts) (hD : AschbacherDichotomy)
    (h27 : Segev27) (h28 : Segev28)
    {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) : F5Local G a z := by
  have iGzOrbit := gzOrbitInput_holds
  have iGzClass := gzClassInput_holds
  have iGzNo := @gzNo_of_hyps
  have iY4a := y4aInput_holds
  have iGz9 := gz9Input_holds
  have iStructGz := structGzInput_holds
  have iStructX := structXInput_holds
  have iTableIII := tableIIIInput_holds
  have iTableIV := tableIVInput_holds
  have iPerp := perpInput_holds
  have iTableV := tableVInput_holds
  have iFourB := @fourB_of_hyps
  have iS7 := @s7Input_holds
  have iSixA := @sixAInput_holds
  have iTableVI := tableVIInput_holds
  have iTableVII := @tableVII_of_hyps
  have iLines := @lines_of_hyps
  have iOddInv := @oddInvInput_holds
  have iGamma := @gamma_of_hyps
  have hF1 : Vert Fusion1Facts a z := fun x w hx hw =>
    fusion1_of_isF5Type hI hS hC (isF5Type_of_isConj h hx hw)
  have hCube : Vert CubeFacts a z := fun x w hx hw =>
    cube_of_fusion1 hI hM (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
  have hA8 : Vert A8Shapes a z := fun x w hx hw =>
    a8Shapes_of_cube hI (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hCube.of_isConj hx hw)
  have hF2 : Vert Fusion2Facts a z := fun x w hx hw =>
    fusion2_of_a8Shapes hI hS (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
      (hA8.of_isConj hx hw)
  have hF3 : Vert Fusion3Facts a z := fun x w hx hw =>
    fusion3_of_fusion2 hI (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
  have hPic : Vert A8Pictures a z := fun x w hx hw =>
    a8Pictures_of_fusion3 hI (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
      (hCube.of_isConj hx hw) (hA8.of_isConj hx hw) (hF2.of_isConj hx hw) (hF3.of_isConj hx hw)
  have hOrb : Vert GzOrbitFacts a z := fun x w hx hw =>
    iGzOrbit hI hC hD (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
      (hF2.of_isConj hx hw) (hF3.of_isConj hx hw)
  have hCls : Vert GzClassFacts a z := fun x w hx hw =>
    iGzClass hI hC (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
      (hF2.of_isConj hx hw) (hF3.of_isConj hx hw) (hOrb.of_isConj hx hw)
  have hNo : Vert GzNoFacts a z := fun x w hx hw =>
    iGzNo hC (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hF3.of_isConj hx hw) (hOrb.of_isConj hx hw) (hCls.of_isConj hx hw)
  have hY4a : Vert Y4aFacts a z := fun x w hx hw =>
    iY4a hI hC (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hCube.of_isConj hx hw)
      (hA8.of_isConj hx hw) (hF2.of_isConj hx hw) (hF3.of_isConj hx hw) (hPic.of_isConj hx hw)
      (hOrb.of_isConj hx hw) (hCls.of_isConj hx hw)
  have hGz9 : Vert Gz9Facts a z := fun x w hx hw =>
    iGz9 hC (isF5Type_of_isConj h hx hw) (hF2.of_isConj hx hw) (hF3.of_isConj hx hw)
      (hOrb.of_isConj hx hw) (hNo.of_isConj hx hw) (hY4a.of_isConj hx hw)
  have hSGz : Vert StructGzFacts a z := fun x w hx hw =>
    iStructGz hI hC (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hF3.of_isConj hx hw) (hPic.of_isConj hx hw) (hOrb.of_isConj hx hw) (hCls.of_isConj hx hw)
      (hY4a.of_isConj hx hw) (hGz9.of_isConj hx hw)
  have hSX : Vert StructXFacts a z := fun x w hx hw =>
    iStructX hI hS (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
      (hF2.of_isConj hx hw) (hF3.of_isConj hx hw) (hPic.of_isConj hx hw) (hOrb.of_isConj hx hw)
      (hY4a.of_isConj hx hw) (hSGz.of_isConj hx hw)
  have hT3 : Vert TableIIIFacts a z := fun x w hx hw =>
    iTableIII hI hS (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
      (hF2.of_isConj hx hw) (hF3.of_isConj hx hw) (hPic.of_isConj hx hw) (hOrb.of_isConj hx hw)
      (hSGz.of_isConj hx hw) (hSX.of_isConj hx hw)
  have hPar : Vert ParityFacts a z := fun x w hx hw =>
    parity_of_fusion3 (isF5Type_of_isConj h hx hw) (hF2.of_isConj hx hw) (hF3.of_isConj hx hw)
  have hT4 : Vert TableIVFacts a z := fun x w hx hw =>
    iTableIV hI hS (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hF3.of_isConj hx hw) (hPic.of_isConj hx hw) (hSGz.of_isConj hx hw) (hSX.of_isConj hx hw)
      (hT3.of_isConj hx hw) (hPar.of_isConj hx hw)
  have hPerp : Vert PerpFacts a z := fun x w hx hw =>
    iPerp hI (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hF3.of_isConj hx hw) (hPic.of_isConj hx hw) (hT3.of_isConj hx hw) (hT4.of_isConj hx hw)
      (hPar.of_isConj hx hw)
  have hT5 : Vert TableVFacts a z := fun x w hx hw =>
    iTableV hI (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hF3.of_isConj hx hw) (hT3.of_isConj hx hw) (hT4.of_isConj hx hw) (hPar.of_isConj hx hw)
      (hPerp.of_isConj hx hw)
  have h4B : Vert FourBFacts a z := fun x w hx hw =>
    iFourB hI (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hF3.of_isConj hx hw) (hPic.of_isConj hx hw) (hPerp.of_isConj hx hw) (hT5.of_isConj hx hw)
  have hS7 : Vert S7Facts a z := fun x w hx hw =>
    iS7 (isF5Type_of_isConj h hx hw) (hCube.of_isConj hx hw) (hF3.of_isConj hx hw)
      (hPic.of_isConj hx hw) (hPar.of_isConj hx hw) (hT4.of_isConj hx hw) (hPerp.of_isConj hx hw)
      (hT5.of_isConj hx hw) (h4B.of_isConj hx hw)
  have h6A : Vert SixAFacts a z := fun x w hx hw =>
    iSixA (isF5Type_of_isConj h hx hw) (hF3.of_isConj hx hw) (hPic.of_isConj hx hw)
      (hT5.of_isConj hx hw) (hS7.of_isConj hx hw)
  have hT6 : Vert TableVIFacts a z := fun x w hx hw =>
    iTableVI hI hS hM (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw)
      (hCube.of_isConj hx hw) (hF2.of_isConj hx hw) (hF3.of_isConj hx hw) (hPic.of_isConj hx hw)
      (hSGz.of_isConj hx hw) (hT3.of_isConj hx hw) (hT5.of_isConj hx hw) (h4B.of_isConj hx hw)
      (hS7.of_isConj hx hw) (h6A.of_isConj hx hw)
  have hT7 : Vert TableVIIFacts a z := fun x w hx hw =>
    iTableVII hS h28 (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hF3.of_isConj hx hw) (hPic.of_isConj hx hw) (hPar.of_isConj hx hw) (hT4.of_isConj hx hw)
      (hT5.of_isConj hx hw) (hS7.of_isConj hx hw) (hT6.of_isConj hx hw)
  have hLines : Vert LinesFacts a z := fun x w hx hw =>
    iLines hU (isF5Type_of_isConj h hx hw) (hF3.of_isConj hx hw) (hCube.of_isConj hx hw)
      (hPic.of_isConj hx hw) (hT4.of_isConj hx hw) (hPerp.of_isConj hx hw) (hT5.of_isConj hx hw)
      (h6A.of_isConj hx hw) (hT7.of_isConj hx hw) (hPar.of_isConj hx hw)
  have hOdd : Vert OddInvFacts a z := fun x w hx hw =>
    iOddInv (isF5Type_of_isConj h hx hw) (hF3.of_isConj hx hw) (hOrb.of_isConj hx hw)
      (hCls.of_isConj hx hw) (hNo.of_isConj hx hw) (hY4a.of_isConj hx hw) (hSGz.of_isConj hx hw)
      (hPar.of_isConj hx hw) (hT5.of_isConj hx hw) (hT7.of_isConj hx hw)
  have hGam : Vert GammaFacts a z := fun x w hx hw =>
    iGamma h27 hU (isF5Type_of_isConj h hx hw) (hCls.of_isConj hx hw) (hF3.of_isConj hx hw)
      (hPar.of_isConj hx hw) (hT4.of_isConj hx hw) (hPerp.of_isConj hx hw) (hT5.of_isConj hx hw)
      (h4B.of_isConj hx hw) (h6A.of_isConj hx hw) (hT7.of_isConj hx hw) (hLines.of_isConj hx hw)
      (hOdd.of_isConj hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw) (hCube.of_isConj hx hw)
      (hOrb.of_isConj hx hw) (hNo.of_isConj hx hw)
  have hCore : Vert FiveCoreFacts a z := fun x w hx hw =>
    fiveCore_of_gamma hI (isF5Type_of_isConj h hx hw) (hF1.of_isConj hx hw) (hF2.of_isConj hx hw)
      (hS7.of_isConj hx hw) (hGam.of_isConj hx hw)
  have hFive : Vert FiveFacts a z := fun x w hx hw =>
    five_of_core hI hU (isF5Type_of_isConj h hx hw) (hCore.of_isConj hx hw) (hCls.of_isConj hx hw)
      (hPar.of_isConj hx hw) (hT4.of_isConj hx hw) (hT5.of_isConj hx hw) (hT6.of_isConj hx hw)
      (hT7.of_isConj hx hw) (hGam.of_isConj hx hw)
  exact
    { fusion1 := hF1,
      cube := hCube,
      a8shapes := hA8,
      fusion2 := hF2,
      fusion3 := hF3,
      a8pictures := hPic,
      gzOrbit := hOrb,
      gzClass := hCls,
      gzNo := hNo,
      y4a := hY4a,
      gz9 := hGz9,
      structGz := hSGz,
      structX := hSX,
      tableIII := hT3,
      parity := hPar,
      tableIV := hT4,
      perp := hPerp,
      tableV := hT5,
      fourB := h4B,
      s7 := hS7,
      sixA := h6A,
      tableVI := hT6,
      tableVII := hT7,
      lines := hLines,
      oddInv := hOdd,
      gamma := hGam,
      five := hFive,
      order := order_of_five hI hS hU h hT5 hT7 hGam hFive }

theorem f5Local_of_isF5Type (hI : TwoHSInterface) (hS : SuborbitFacts) (hC : CSideFacts)
    (hM : M11Facts) (hU : U35Facts) (hD : AschbacherDichotomy) (h27 : Segev27)
    {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z) : F5Local G a z :=
  f5Local_of_isF5Type_of_inputs hI hS hC hM hU hD h27 segev28_holds h

end CFSG.EvenSporadicStandard.HNRecog.Section3
