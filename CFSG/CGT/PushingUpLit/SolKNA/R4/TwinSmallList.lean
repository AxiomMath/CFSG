module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallSp4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallRee
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallL4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallU4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallL5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallU5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallExc
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpMainR

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.GH74.KGroups CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.CatFactsSmall CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4


structure TwinLeavesR (r n : ℕ) : Prop where
  g23 : TwinLeafR r n fun F _ => LieModel F .G2 0 3 1
  d43 : TwinLeafR r n fun F _ => LieModel F .trialityD4 0 3 1
  l43 : TwinLeafR r n fun F _ => LieModel F .PSL 4 3 1
  u43 : TwinLeafR r n fun F _ => LieModel F .PSU 4 3 1
  l53 : TwinLeafR r n fun F _ => LieModel F .PSL 5 3 1
  excluded : TwinLeafR r n ExcludedRest

theorem twinPerpSmallR_of_list (hList : SmallListR) {r : ℕ} (hr : 4 ≤ r) (n : ℕ)
    (hL : TwinLeavesR r n) : TwinPerpSmallR r n := by
  intro Y _ _ R S t hP hsmall
  haveI := hP.core.simple
  rcases hList _ hP.core.nonab hsmall with hfam | hex
  · unfold SmallFamily at hfam
    rcases hfam with h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact twinLeafR_g2 hr hL.g23 Y R S t hP hsmall h
    · exact twinLeafR_d4 hr hL.d43 Y R S t hP hsmall h
    · exact twinLeafR_psp4 hr twinLeafR_psp4Ne3 Y R S t hP hsmall h
    · exact twinLeafR_twistedG2 hr Y R S t hP hsmall h
    · exact twinLeafR_l4 hL.l43 Y R S t hP hsmall h
    · exact twinLeafR_u4 hL.u43 Y R S t hP hsmall h
    · exact twinLeafR_l5 hr hL.l53 Y R S t hP hsmall h
    · exact twinLeafR_u5 hr Y R S t hP hsmall h
    · exact twinLeafR_m12 hr Y R S t hP hsmall h
    · exact twinLeafR_l2 hr Y R S t hP hsmall h
    · exact twinLeafR_l3 hr Y R S t hP hsmall h
    · exact twinLeafR_u3 hr Y R S t hP hsmall h
    · exact twinLeafR_m11 hr Y R S t hP hsmall h
  · rcases excludedSmall_split hex with h | h | h
    · exact twinLeafR_exAlt hr Y R S t hP hsmall h
    · exact twinLeafR_exL2Even hr Y R S t hP hsmall h
    · exact hL.excluded Y R S t hP hsmall h

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
