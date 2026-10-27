module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CentLe3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8TwoConn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3

section CentLe


theorem l3e8_cent_le_two {T : Type} [Group T] [Finite T] [CaseIAmbient T] {K : Subgroup T}
    {z : T} {J : Subgroup T} {zJ : T} {H Q E S : Subgroup T} (cfg : L3E8Cfg K z J zJ H Q E S)
    (hU : UniqueCosetZ K z) (_h2 : L3E8TwoFactors K) (hcit : CIT3Below (Nat.card T))
    (hP : TL4.TightBelowRPlus 3 (Nat.card T)) : L3E8CentLe K z :=
  cfg.cent_le_of_pkg hU hcit hP

theorem l3e8_cent_le {T : Type} [Group T] [Finite T] [CaseIAmbient T] {K : Subgroup T} {z : T}
    {J : Subgroup T} {zJ : T} {H Q E S : Subgroup T} (cfg : L3E8Cfg K z J zJ H Q E S)
    (hU : UniqueCosetZ K z) (hcit : CIT3Below (Nat.card T))
    (hP : TL4.TightBelowRPlus 3 (Nat.card T)) : L3E8CentLe K z :=
  cfg.cent_le_of_twoFactors_case fun h2 => l3e8_cent_le_two cfg hU h2 hcit hP

end CentLe

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
