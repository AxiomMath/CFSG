module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallExc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall


theorem leaf_exRest {n : ℕ}
    (hu34 : TwinLeafS n fun F _ => CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2)
    (hl34 : TwinLeafS n fun F _ => LieModel F .PSL 3 2 2)
    (hsz8 : TwinLeafS n fun F _ => LieModel F .twistedB2 0 2 3)
    (hm22 : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .M22)
    (hm23 : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .M23)
    (hj1 : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .J1)
    (hj2 : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .J2)
    (hj3 : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .J3)
    (hmcl : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .McL)
    (hly : TwinLeafS n fun F _ => NativeSporadic.IsSporadic F .Ly) :
    TwinLeafS n ExcludedRest := by
  intro Y _ _ R S t h hsmall hF
  rcases hF with hF | hF | hF | hF | hF | hF | hF | hF | hF | hF
  · exact hu34 Y R S t h hsmall hF
  · exact hl34 Y R S t h hsmall hF
  · exact hsz8 Y R S t h hsmall hF
  · exact hm22 Y R S t h hsmall hF
  · exact hm23 Y R S t h hsmall hF
  · exact hj1 Y R S t h hsmall hF
  · exact hj2 Y R S t h hsmall hF
  · exact hj3 Y R S t h hsmall hF
  · exact hmcl Y R S t h hsmall hF
  · exact hly Y R S t h hsmall hF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
