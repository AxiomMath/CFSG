module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Psl

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem core911_l3 : Core911L3 := by
  intro Y _ _ _ _ h
  obtain ⟨p, f, hp, hf, hp2, hL⟩ := h
  exact no911_psl (by norm_num) hp2 hL hp hf

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
