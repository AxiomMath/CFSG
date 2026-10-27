module

public import CFSG.GH74.Generic.BProg.B2.Thm2Done
public import CFSG.GH74.Generic.BProg.B2.Assembly1
public import CFSG.GH74.Generic.BProg.B2.Prop31
public import CFSG.GH74.Generic.BProg.Stage2Allow
public import CFSG.GH74.Generic.BProg.B1.NontrivNonsolv

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.ComponentClassification.TBLit

theorem stage2Allow_of_open
    (hS : B1.Stage1NontrivSolv) (hB : Stage1Bal) (t1 : Stage2Thm1)
    (t3 : Stage2Thm3) (t4 : Stage2Thm4) : Stage2Allow :=
  stage2Allow_of_thms
    (B1.stage1Nontriv_of_branches (B1.stage1NontrivNonsolv_of_b2 GLS.b_B2_g4_proved) hS) hB t1
    stage2Thm2_proved t3 (stage2Prop31_proved GLS.b_B2_g4_proved) t4

theorem b_Gen4_liftJ2NS_of_open
    (hGA : GriessMultipliersAllModels) (hS : B1.Stage1NontrivSolv)
    (hB : Stage1Bal) (t1 : Stage2Thm1) (t3 : Stage2Thm3) (t4 : Stage2Thm4) : B_Gen4_liftJ2NS :=
  b_Gen4_liftJ2NS_of_allow (genericKnownFacts_of_griess hGA) (stage2Allow_of_open hS hB t1 t3 t4)

end CFSG.GH74.Generic.BProg.B2
