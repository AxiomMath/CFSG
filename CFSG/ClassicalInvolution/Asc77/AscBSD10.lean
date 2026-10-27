module

public import CFSG.ClassicalInvolution.Asc77.AscBSD6
public import CFSG.ClassicalInvolution.Asc77.AscBSD9
public import CFSG.ClassicalInvolution.Asc77.AscBSD8

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem bootNoManyTwins (hD4 : BootNoManyTwinsD4 p f) : BootNoManyTwins p f :=
  bootNoManyTwins_of_models (fun t n hl hnot => by
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fundTwoBound_psp_two
    · exact fundTwoBound_psl_four
    · exact fundTwoBound_psu_four
    · exact fundTwoBound_odd_three
    · exact absurd ⟨rfl, rfl⟩ hnot
    · exact fundTwoBound_minus_four) hD4

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
