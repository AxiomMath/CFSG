module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23D03
public import CFSG.ClassicalInvolution.Q3.Q3T7S23DY02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77


theorem d4YSide_of_oddCore (hOY : OddCoreLayer23Plus3) : D4YSide := by
  intro G _ _ _ Ω K K' W z u e g h hα hE hY6 hex hOE
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := Q3T8.Asc77.Hyp23.setting h.std
  have hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g := Q3T8.Asc77.Hyp23b.data h
  obtain ⟨K₁, z₁, hD⟩ := ySideD4_3 hs hd hex
    (hOY G Ω K K' W z u e g h hα hE hY6 hex hOE) hY6
  exact ⟨K₁, z₁, hD.mem, hD.inv, hD.le, hD.pair, hD.gen, hD.comm, hD.chart, hD.chart', hD.fix⟩

theorem d4Chain23_of_oddCore
    (hO : OddCoreLayer23Neg3) (hOY : OddCoreLayer23Plus3) : D4Chain23 :=
  d4Chain23_of_yside hO (d4YSide_of_oddCore hOY)

end CFSG.ClassicalInvolution.Q3.Q3T7S23
