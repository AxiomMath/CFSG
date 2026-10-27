module

public import CFSG.CGT.Timmesfeld75.FinalNode
public import CFSG.CGT.Timmesfeld75.SimpleFromA
public import CFSG.CGT.Timmesfeld75.ListWCCert
public import CFSG.CGT.Timmesfeld75.GoldschmidtMilestone
public import CFSG.Timmesfeld.CorollaryB
public import CFSG.CGT.T75N.A9Weak
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.Small64
public import CFSG.CGT.T75D.Assemble
public import CFSG.CGT.T75E.RootGroup
public import CFSG.CGT.T75E.Lemma26
public import CFSG.CGT.T75G.Sec68Insp
public import CFSG.CGT.T75F.Sec57Shult
public import CFSG.CGT.T75K.A6
public import CFSG.CGT.T75O.Done
public import CFSG.CGT.T75M.StageD
public import CFSG.CGT.T75M.StageKL
public import CFSG.CGT.T75JM.L2Cert
public import CFSG.CGT.T75JM.M22PDCert
public import CFSG.CGT.T75JM.PCert
public import CFSG.CGT.T75M23.M23Final

public section

namespace CFSG.CGT.Timmesfeld75

structure NodeInputsRest : Prop where
  a8Sylow : CFSG.CGT.T75P.A8SylowInput
  m24Sylow : CFSG.CGT.T75P.M24SylowInput

theorem NodeInputsRest.toFlat (I : NodeInputsRest) : NodeInputs :=
  have h214 := lemma214_of_remaining
    { aschbacherTheoremOne := CFSG.Timmesfeld.Bridge.Asc72.theoremOne
      benderCenter := CFSG.CGT.T75N.benderCenterInput
      unitaryTwoGeneration := CFSG.CGT.T75N.unitaryTwoGenerationInput }
  { aschbacherTheoremOne := CFSG.Timmesfeld.Bridge.Asc72.theoremOne
    goldschmidt := goldschmidt1974_of_milestone
    corB := CFSG.Timmesfeld.timmesfeldCorBInput
    benderCenter := CFSG.CGT.T75N.benderCenterInput
    unitaryTwoGeneration := CFSG.CGT.T75N.unitaryTwoGenerationInput
    lemma26 := CFSG.CGT.T75E.lemma26
    rootGroup := CFSG.CGT.T75E.rootGroup_of_simple CFSG.CGT.T75E.lemma26Simple
    shult := CFSG.CGT.T75F.sec57Shult_of_goldschmidt goldschmidt1974_of_milestone
    corB56 := CFSG.CGT.T75O.sec56CorB_of_listWC listWCIdentification_of_cert
    ins68 := CFSG.CGT.T75G.sec68Inspection_direct
    listWC := listWCIdentification_of_cert
    a9 := CFSG.CGT.T75N.a9Input_weak
    small64 := CFSG.CGT.T75N.small64Input
    szThree := T75M.section3SzInput_of_triangle aschbacherNoPolarInput_of_repo
        CFSG.Timmesfeld.Bridge.Asc72.theoremOne h214 involutionClassInput_of_repo
        (T75M.szTriangleInput_of_lemma26 h214 involutionClassInput_of_repo lemma215
            CFSG.CGT.T75E.lemma26)
    noLayer := CFSG.CGT.T75D.noLayer_of_inputs goldschmidt1974_of_milestone
      CFSG.Timmesfeld.Bridge.Asc72.theoremOne h214
    a6 := CFSG.CGT.T75K.sec63A6_of_inputs lemma215 CFSG.CGT.T75E.lemma26
    jankoM22 := T75JM.jankoM22CtxInput_of_parts T75JM.l2Statement_of_certificate
        T75JM.pStatement_of_certificate T75JM.r22PDStatement_of_certificate
    jankoM23 := CFSG.CGT.T75M23.jankoM23CtxInput_of_certificates
    a8Sylow := I.a8Sylow
    m24Sylow := I.m24Sylow }

theorem theoremA_final_rest (I : NodeInputsRest) : TheoremAStmt :=
  theoremA_final I.toFlat

theorem node_final_rest (I : NodeInputsRest) : NodeStatement :=
  node_final I.toFlat

theorem simpleCaseListStmt_final_rest (I : NodeInputsRest) : SimpleCaseListStmt :=
  simpleCaseListStmt_of_theoremA (theoremA_final_rest I)

end CFSG.CGT.Timmesfeld75
