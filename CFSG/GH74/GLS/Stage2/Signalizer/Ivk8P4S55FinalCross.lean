module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Comp5Split
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1All
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPG2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55OrdPSp
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3G2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3LNoRC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3U4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem cross55_leaves
    (hOrd3U3 : Ord3 FU3d) (hOrd3D4 : D4Ord3)
    (hOrdPU3 : OrdPInner FU3d) (hOrdPD4 : OrdPInner FD4d)
    (hOrdPU4 : OrdPInner FU4d) (hOrdPRee : OrdPInner FReed)
    (hC2 : Comp5m2Types) (hC1 : Comp5m1Types) : Cross55 :=
  cross55_of_steps (stepL2_of crossE1_all)
    (stepH3_of crossE1_all
      ⟨ord3_fl3d_closed, hOrd3U3, ord3_fsp4d, ord3_fg2d, hOrd3D4, ord3_fl4d, ord3_fu4d⟩)
    (stepH5_of crossE1_all crossE2_thm
      ⟨ordPInner_fl3d, hOrdPU3, ordPInner_fsp4d, ordPInner_fg2d, hOrdPD4, ordPInner_fl4d,
        hOrdPU4, hOrdPRee⟩
      (comp5Types_of_split hC2 hC1))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
