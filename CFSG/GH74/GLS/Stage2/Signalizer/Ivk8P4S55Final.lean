module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Asm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BridgeThm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGEnd
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FinalBase
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FinalCross
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FinalParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MSpor
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPU
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3U3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8


theorem lemma5_5m_leaves (hOrd3D4 : D4Ord3) (hOrdPD4 : OrdPInner FD4d)
    (hOrdPRee : OrdPInner FReed) (hC2 : Comp5m2Types) (hC1 : Comp5m1Types)
    (hB : Case55B) : Lemma5_5m :=
  lemma5_5m_of
    (frame55thm_of_parts (bridge55_thm final_hSch final_hL31 final_hInv)
      (endgame55_of final_hInv (endgameL3_thm final_hInv)))
    hB
    (cells55_leaves
      (cross55_leaves ord3_fu3d hOrd3D4 ordPInner_fu3d hOrdPD4 ordPInner_fu4d hOrdPRee hC2 hC1)
      (cell55_of_n1 multAlt55 n1fam_spor))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
