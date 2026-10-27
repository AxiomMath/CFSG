module

public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.CGT.Timmesfeld75.Sec213
public import CFSG.CGT.Timmesfeld75.Sec215
public import CFSG.CGT.Timmesfeld75.SimpleAssembly
public import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.CGT.Timmesfeld75.Lemma214Transfer

public section

namespace CFSG.CGT.Timmesfeld75

structure LiteratureInputs : Prop where
  aschbacherNoPolar : AschbacherNoPolarInput
  aschbacherTheoremOne : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne
  benderCenter : BenderCenterInput
  unitaryTwoGeneration : UnitaryTwoGenerationInput
  benderSimple : BenderSimpleInput
  benderList : BenderListInput
  benderTransitive : BenderTransitiveInput

structure PaperStepInputs : Prop where
  step57 : Step57
  step511 : Step511
  step69 : Step69
  step68 : Step68
  step610 : Step610
  step79 : Step79
  step711 : Step711
  step81 : Step81
  step82 : Step82

theorem lemma215_of_literature (L : LiteratureInputs) : Lemma215Stmt :=
  lemma215_of_inputs lemma213 L.benderSimple L.aschbacherTheoremOne

theorem lemma214_of_literature (L : LiteratureInputs) : Lemma214 :=
  lemma214_of_core (core214_of_inputs L.aschbacherNoPolar L.benderCenter L.unitaryTwoGeneration)

theorem simpleCaseStmt_of_inputs (L : LiteratureInputs) (P : PaperStepInputs) : SimpleCaseStmt :=
  simpleCaseStmt_of_steps L.aschbacherNoPolar L.benderList L.benderTransitive P.step57
    P.step511 P.step69 P.step68 P.step610 P.step79 P.step711 P.step81 P.step82

theorem theoremA_of_inputs (L : LiteratureInputs) (P : PaperStepInputs) : TheoremAStmt :=
  theoremAStmt_of_inputs (simpleCaseStmt_of_inputs L P) (lemma215_of_literature L)

theorem node_of_inputs (L : LiteratureInputs) (P : PaperStepInputs) : NodeStatement :=
  nodeStatement_of_simpleCase (simpleCaseStmt_of_inputs L P).list

end CFSG.CGT.Timmesfeld75
