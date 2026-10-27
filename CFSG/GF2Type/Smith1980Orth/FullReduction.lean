module

public import CFSG.GF2Type.Smith1980Orth.SixFinal
public import CFSG.GF2Type.Smith1980Orth.W4Assembly
public import CFSG.GF2Type.Smith1980Orth.W4SigmaStep
public import CFSG.GF2Type.Smith1980Orth.IdentW4
public import CFSG.LargeExtraspecial.DWW4ThmA
public import CFSG.Holt.H78.Theorem1
public import CFSG.Holt.H78.Bridge
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Quasithin.H13.L32NSp4Over

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

theorem smith1980Orthogonal_of_w4Inputs' (I : TimInputs)
    (hAS4 : CFSG.LargeExtraspecial.S14.AschbacherSmithW4Input) (I4 : W4Inputs) :
    Smith1980OrthogonalStatement :=
  smith1980Orthogonal_of_six_of_four
    (smith1980OrthogonalSix_of_timInputs I
      (CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1)
      identInput)
    (smith1980OrthogonalW4_of_inputs
      (CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1)
      altInput identW4Input
      (fourW4Input_of_thmA hAS4 CFSG.LargeExtraspecial.DW.W4Rank.theoremAWidthFour_holds)
      I4)

theorem smith1980Orthogonal_of_timInputs (I : TimInputs)
    (hAS4 : CFSG.LargeExtraspecial.S14.AschbacherSmithW4Input) : Smith1980OrthogonalStatement :=
  smith1980Orthogonal_of_w4Inputs' I hAS4
    (w4Inputs I hAS4 CFSG.LargeExtraspecial.DW.W4Rank.theoremAWidthFour_holds W4.pgl25W4Free)

end CFSG.GF2Type.Smith1980Orth
