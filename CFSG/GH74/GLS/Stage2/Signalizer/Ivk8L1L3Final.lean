module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Card
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Rank
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Sec
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1CardL3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem cellAbs_FL3 : CellAbs FL3 :=
  cellAbs_FL3_of_facts
    { card := fun _ _ _ _ _ hp hf hp2 hLie => fl3_card_formula hp hf hp2 hLie
      not_dvd := fun _ _ _ hY => not_card_dvd_factorial_of_FL3 hY
      sec := fun _ _ _ _ _ hp hf hp2 hLie => fl3_L2_section hp hf hp2 hLie
      aut := fun _ _ _ _ _ hp hf hp2 hLie => fl3_card_aut_dvd hp hf hp2 hLie
      rank := fun _ _ _ _ _ hp hf hp2 hLie => fl3_elemAbelian_le_four hp hf hp2 hLie }

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
