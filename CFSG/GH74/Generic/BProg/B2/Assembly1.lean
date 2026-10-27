module

public import CFSG.GH74.Generic.BProg.B1.JPrime
public import CFSG.GH74.Generic.BProg.B1.PilotS1Three
public import CFSG.GH74.Generic.BProg.B1.PilotS4
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankNS
public import CFSG.GH74.Generic.BProg.B1.Stage3aSD5

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg

theorem sourceExists_proved :
    SourceExists :=
  B1.sourceExists_of_shapes B1.sourceExistsFor_shape1 B1.sourceExistsFor_shape3
    B1.sourceExistsFor_shape4 B1.sourceExistsFor_shape5

theorem admissibleExists_proved :
    AdmissibleExists :=
  B1.admissibleExists_of_shapes B1.admissibleExistsFor_shape1 B1.admissibleExistsFor_shape3
    B1.admissibleExistsFor_shape4 B1.admissibleExistsFor_shape5

theorem b_Gen4_liftJ2NS_of_allow
    (hF : GenericKnownFacts) (hAllow : Stage2Allow) : B_Gen4_liftJ2NS :=
  B1.b_Gen4_liftJ2NS_of_noJPrime
    (stage2QSNS_of_allow sourceExists_proved admissibleExists_proved hAllow)
    (B1.jPrimeNS_of_known_facts hF)
    (B1.noJPrime_of_shape3SD (B1.noJPrimeShape3SD_of_allow hAllow))

end CFSG.GH74.Generic.BProg.B2
