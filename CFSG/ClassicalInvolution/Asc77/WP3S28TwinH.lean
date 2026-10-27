module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinC
public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinE
public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinF
public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinG

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.Assembly.LowTwoRank

local notation "𝒞" => CoreAssembly.conjClass

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem twinProductCentral_of_row {tY : StatedLieTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hadm : StatedLieAdmissible tY nY p f) :
    TwinProductCentral p f tY nY := by
  rcases hrow with ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ |
    ⟨-, rfl, rfl⟩
  · exact twinProductCentral_plus hp2 hq hadm
  · exact twinProductCentral_psl4 hp2 hq hadm
  · exact twinProductCentral_odd hp2 hq hadm
  · exact twinProductCentral_psp2 hp2 hq hadm
  · exact twinProductCentral_minus hp2 hq hadm
  · exact twinProductCentral_psu4 hp2 hq hadm

theorem twinInvolution_proved : Asc77.TwinInvolution p f := by
  intro G _ _ _ hnab K z S tY nY hrow hshape T hT
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape hrow.tag_facts.2.1
  exact twinInvolutionRow hrow (twinProductCentral_of_row hrow S.odd S.five hadm) hnab S hshape hT

end Main

end CFSG.ClassicalInvolution.Asc77.S28
