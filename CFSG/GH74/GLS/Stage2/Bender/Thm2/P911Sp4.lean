module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Psp

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem core911_sp4 : Core911Sp4 := by
  intro Y _ _ _ _ h
  obtain ⟨p, f, -, -, hp2, hL⟩ := h
  exact no911_psp le_rfl hp2 hL

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
