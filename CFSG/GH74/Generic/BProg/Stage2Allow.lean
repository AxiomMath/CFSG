module

public import CFSG.GH74.Generic.BProg.Stage2Assembly
public import CFSG.GH74.Generic.BProg.Stage1Split
public import CFSG.GH74.Generic.BProg.PQExists
public import CFSG.GH74.Generic.BProg.Cor2

public section

namespace CFSG.GH74.Generic.BProg

theorem stage2Allow_of_thms
    (hN : Stage1Nontriv) (hB : Stage1Bal) (t1 : Stage2Thm1) (t2 : Stage2Thm2)
    (t3 : Stage2Thm3) (p31 : Stage2Prop31) (t4 : Stage2Thm4) : Stage2Allow :=
  stage2Allow_of_level2 (stage1Alt_of_parts hN hB) stage2PQExists_proved t1 t2 stage2Cor2_proved t3
    p31 t4

end CFSG.GH74.Generic.BProg
