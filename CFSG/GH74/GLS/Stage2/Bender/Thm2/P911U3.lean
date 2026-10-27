module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Psu

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem core911_u3 : Core911U3 := by
  intro Y _ _ _ _ h
  obtain ⟨p, f, -, -, hp2, hL⟩ := h
  exact no911_psu (by norm_num) hp2 hL

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
