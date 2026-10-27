module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallExc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfMain

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TA3 CFSG.Blueprint
  CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

set_option linter.unusedSectionVars false


structure TwinLeavesS (n : ℕ) : Prop where
  g2Ne3 : TwinLeafS n SmallG2Ne3
  g23 : TwinLeafS n fun F _ => LieModel F .G2 0 3 1
  d4Ne3 : TwinLeafS n SmallD4Ne3
  d43 : TwinLeafS n fun F _ => LieModel F .trialityD4 0 3 1
  psp4Ne3 : TwinLeafS n SmallPSp4Ne3
  psp43 : TwinLeafS n fun F _ => LieModel F .PSp 2 3 1
  twistedG2 : TwinLeafS n SmallTwistedG2
  l4Ne3 : TwinLeafS n SmallL4Ne3
  l43 : TwinLeafS n fun F _ => LieModel F .PSL 4 3 1
  u4Ne3 : TwinLeafS n SmallU4Ne3
  u43 : TwinLeafS n fun F _ => LieModel F .PSU 4 3 1
  l5Ne3 : TwinLeafS n SmallL5Ne3
  l53 : TwinLeafS n fun F _ => LieModel F .PSL 5 3 1
  u5 : TwinLeafS n SmallU5
  m12 : TwinLeafS n SmallM12
  l2 : TwinLeafS n SmallL2
  l3Ne3 : TwinLeafS n SmallL3Ne3
  l33 : TwinLeafS n fun F _ => LieModel F .PSL 3 3 1
  u3Ne3 : TwinLeafS n SmallU3Ne3
  u33 : TwinLeafS n fun F _ => LieModel F .PSU 3 3 1
  m11 : TwinLeafS n SmallM11
  exAlt : TwinLeafS n ExAlt
  exL2Even : TwinLeafS n ExL2Even
  exRest : TwinLeafS n ExcludedRest

theorem twinPerpSmallE_of_list (hList : SmallListR) (n : ℕ) (hL : TwinLeavesS n) :
    TwinPerpSmallE n := by
  intro Y _ _ R S t hP hsmall
  haveI := hP.core.simple
  rcases hList _ hP.core.nonab hsmall with hfam | hex
  · unfold SmallFamily at hfam
    rcases hfam with h | h | h | h | h | h | h | h | h | h | h | h | h
    ·
      refine (TwinLeafS.of_split (P := SmallG2) (fun F _ hF => ?_) hL.g23 hL.g2Ne3) Y R S t hP
        hsmall h
      obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl hm
      · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩
    ·
      refine (TwinLeafS.of_split (P := SmallD4) (fun F _ hF => ?_) hL.d43 hL.d4Ne3) Y R S t hP
        hsmall h
      obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl hm
      · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩
    ·
      refine (TwinLeafS.of_split (P := SmallPSp4) (fun F _ hF => ?_) hL.psp43 hL.psp4Ne3) Y R S t
        hP hsmall h
      obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl hm
      · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩
    · exact hL.twistedG2 Y R S t hP hsmall h
    ·
      refine (TwinLeafS.of_split (P := SmallL4) (fun F _ hF => ?_) hL.l43 hL.l4Ne3) Y R S t hP
        hsmall h
      obtain ⟨p, f, hp, hp2, hf, h8, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl hm
      · exact Or.inr ⟨p, f, hp, hp2, hf, h8, h3, hm⟩
    ·
      refine (TwinLeafS.of_split (P := SmallU4) (fun F _ hF => ?_) hL.u43 hL.u4Ne3) Y R S t hP
        hsmall h
      obtain ⟨p, f, hp, hp2, hf, h8, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl hm
      · exact Or.inr ⟨p, f, hp, hp2, hf, h8, h3, hm⟩
    ·
      refine (TwinLeafS.of_split (P := SmallL5) (fun F _ hF => ?_) hL.l53 hL.l5Ne3) Y R S t hP
        hsmall h
      obtain ⟨p, f, hp, hp2, hf, h4, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl hm
      · exact Or.inr ⟨p, f, hp, hp2, hf, h4, h3, hm⟩
    · exact hL.u5 Y R S t hP hsmall h
    · exact hL.m12 Y R S t hP hsmall h
    · exact hL.l2 Y R S t hP hsmall h
    ·
      refine (TwinLeafS.of_split (P := SmallL3) (fun F _ hF => ?_) hL.l33 hL.l3Ne3) Y R S t hP
        hsmall h
      obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl (Or.inl ⟨by decide, hm⟩)
      · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩
    ·
      refine (TwinLeafS.of_split (P := SmallU3) (fun F _ hF => ?_) hL.u33 hL.u3Ne3) Y R S t hP
        hsmall h
      obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        exact Or.inl (Or.inl ⟨by decide, hm⟩)
      · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩
    · exact hL.m11 Y R S t hP hsmall h
  · rcases excludedSmall_split hex with h | h | h
    · exact hL.exAlt Y R S t hP hsmall h
    · exact hL.exL2Even Y R S t hP hsmall h
    · exact hL.exRest Y R S t hP hsmall h

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
