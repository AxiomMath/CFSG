module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Final

public section

namespace CFSG.ComponentClassification.GSThmB

structure Lemma81Inputs' : Prop where
  in81 : In81
  cfi : CFProp23IndexReduced
  ac : CFAutSmallCommutator
  aq : CFAutSmallQuotient
  st : SuzukiTausskyInput
  jo : CFSec8JOrder
  f2 : CFSp4F2
  l0 : CF81L0
  conf : CF81Conf
  noNilp : CF81NoNilp
  fieldOrd : CF81FieldOrd
  diag : CF81Diag
  step3 : GS81Step3Input
  step9 : GS81Step9Input
  exit6 : GS81Exit6Input
  exit10 : GS81Exit10Input
  exit11 : GS81Exit11Input
  gh74 : ClassicalInvolution.GH74SectionalModels
  ci : GSLit.ClassicalInvolutionInput
  rs : RestrictedStandardInput

theorem lemma81'
    (I : Lemma81Inputs') :
    Lemma81StatementK :=
  lemma81
    { in81 := I.in81
      cfi := I.cfi
      ac := I.ac
      aq := I.aq
      st := I.st
      jo := I.jo
      f2 := I.f2
      l0 := I.l0
      conf := I.conf
      noNilp := I.noNilp
      fieldOrd := I.fieldOrd
      diag := I.diag
      step3 := I.step3
      step8 := gs81Step8Input_of_in81 I.in81
      step9 := I.step9
      exit6 := I.exit6
      exit10 := I.exit10
      exit11 := I.exit11
      gh74 := I.gh74
      ci := I.ci
      rs := I.rs }

end CFSG.ComponentClassification.GSThmB
