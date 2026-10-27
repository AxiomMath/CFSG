module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLiftCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLiftPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBLiftType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCentK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCentB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82FactE64_holds : Asc82FactE64 := by
  intro G _ _ L hL P hP
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨fr, hfr⟩ := sec4I_exists_frame_good (sec4IRho_isSylow2Of hL e hP)
  exact ⟨sec4ILiftB e fr P, sec4ILiftPhi e fr P,
    { isMax := sec4ILift_isMax hL e hP hfr
      unique := sec4ILift_unique hL e hP hfr
      card := sec4ILift_card hL e hP hfr
      cent := sec4ILift_cent hL e hP hfr
      perm := sec4ILift_perm hL e hP hfr
      type2 := sec4ILift_type2 hL e hP hfr
      type4 := sec4ILift_type4 hL e hP hfr
      type6 := sec4ILift_type6 hL e hP hfr
      centK := sec4ILift_centK hL e hP hfr }⟩

theorem asc82FactCentB_holds : Asc82FactCentB := by
  intro G _ _ L hL P B hP hB _ x hx hxB
  exact sec4I_centB hL hP hB hx hxB

end CFSG.OddStandard.SmallF3.Omega
