module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

private theorem noncomm_UT3c : ∃ a b : UT3 F4c, a * b ≠ b * a := by
  decide +kernel

theorem sylSL_nonabelian : ∃ a b : SylSL3_4, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := noncomm_UT3c
  exact ⟨sylLCongr.symm a, sylLCongr.symm b, fun h => hab (by
    have := congrArg sylLCongr h
    simpa using this)⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
