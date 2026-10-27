module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResP
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinAlt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinBen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinM12
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinM23
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinJ2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinJ3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinL34
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FinalCross
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPU
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Final
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Bridge
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Main

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

theorem cross55_proved : Cross55 :=
  cross55_leaves ord3_fu3d OddStandard.GH71.S55.d4Ord3 ordPInner_fu3d
    OddStandard.GH71.S55.ordPInner_fd4d ordPInner_fu4d OddStandard.GH71.S55.ordPInner_freed
    OddStandard.GH71.S55.comp5m2Types_proved OddStandard.GH71.S55.comp5m1Types_proved

theorem case55b_proved : Case55B :=
  case55b_of_inputs
    { sp4 := cellV_fsp4 final_hInv cross55_proved
      l4 := cellV_fl4 final_hInv cross55_proved
      u4 := cellV_fu4 final_hInv cross55_proved
      a7 := fun _ _ h => finCellA_a7 h
      alt := fun _ h8 h11 _ _ h => finCellB_alt h8 h11 h
      m12 := fun _ _ h => finCellB_m12 h
      m22 := fun _ _ h => finCellB_m22 h
      m23 := fun _ _ h => finCellB_m23 h
      j2 := fun _ _ h => finCellB_j2 h
      j3 := fun _ _ h => finCellB_j3 h
      l216 := fun _ _ h => finCellB_l216 h
      l34 := fun _ _ h => finCellB_l34 h
      u34 := fun _ _ h => finCellB_u34 h
      res := resB_proved }

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
