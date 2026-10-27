module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLarge
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieSmall
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLiePosL3
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLiePosU3
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLiePosG2
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLie3Table
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTExcTw
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLT3D4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ClassicalInvolution.Q3

section Final


theorem lie3Table_holds : Lie3Table :=
  lie3Table_of_rows (lie3At_of_kill (by decide) (by decide) kill3At_twistedE6)
    (lie3At_trialityD4 0)

theorem quaternionInspectionLie_of_cit3_neg (hN : Neg3Table) (h1 : CIT3Inductive)
    (h2 : TightLiftSimple) : QuaternionInspectionLie :=
  quaternionInspectionLie_of_ranges
    (qlSmall_of_small3 (small3Table_of_pos_neg (pos3Table_of_three posModel_L3 posModel_U3
        posModel_G2) hN))
    (qlLarge_of_lift h1 h2 lie3Table_holds (pos3Table_of_three posModel_L3 posModel_U3 posModel_G2))

end Final

end CFSG.CGT.PushingUpLit.SolKNA
