module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Transfer
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Assembly
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltSeven
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L2Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1U3Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sp4Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12G2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12L4Full
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12L5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12U5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Ree
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Cells

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.Stage2.Bender.Thm2


theorem ivk812CoreA_thm : IVK812CoreA :=
  ivk812CoreA_of aframe_thm ⟨cellAbs_Alt, cellAbs_FSpor, cellAbs_FMcLy, cellAbs_FTwo,
    L1.cellAbs_FL2, L1.cellAbs_FL3, L1.cellAbs_FU3, cellAbs_Sp4, cellAbs_G2, cellAbs_D4,
    cellAbs_L4_full, cellAbs_U4_full, cellAbs_L5, cellAbs_U5, cellAbs_Ree⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
