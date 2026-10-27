module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB06
public import CFSG.ClassicalInvolution.Q3.Q3AMDB07
public import CFSG.ClassicalInvolution.Q3.Q3AMDB12
public import CFSG.ClassicalInvolution.Q3.Q3AMDB14

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Final


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem PspSetting.noA2Syl_proved (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) : PspNoA2Syl Ω z := by
  intro L hL l hl hlz hcomm
  by_contra hno
  obtain ⟨L', e, hL', he, hez, hcomm', hno', hcase⟩ :=
    hset.exists_normalized_partner hD hL hl hlz hcomm
  have hno'' := hno' hno
  rcases hcase with hct | hsw
  · exact hset.false_of_commuting_partner hD hL' he hez hcomm' hct hno''
  · exact hset.false_of_swap_partner hL' he hez hcomm' hsw hno''

theorem pspNoA2ResidualSyl_proved : PspNoA2ResidualSyl :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hset hD => hset.noA2Syl_proved hD

theorem pspNoA2Residual_proved : PspNoA2Residual :=
  pspNoA2Residual_of_syl pspNoA2ResidualSyl_proved

theorem c28_DoubleB_proved : C28_DoubleB :=
  c28_DoubleB_of_noA2 pspNoA2Residual_proved

end Final

end CFSG.ClassicalInvolution.Q3.Q3AM
