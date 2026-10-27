module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81FinalA8
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9e
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SuzTau

public section

namespace CFSG.ComponentClassification.GSThmB

structure Lemma81Inputs'' : Prop where
  in81 : In81
  cfi : CFProp23IndexReduced
  ac : CFAutSmallCommutator
  aq : CFAutSmallQuotient
  jo : CFSec8JOrder
  f2 : CFSp4F2
  l0 : CF81L0
  conf : CF81Conf
  noNilp : CF81NoNilp
  fieldOrd : CF81FieldOrd
  diag : CF81Diag
  step3 : GS81Step3Input
  centPerfect : CF81L2CentPerfect
  nineCent : CF81L2NineCent
  sp4Three : CF81Sp4Three
  exit6 : GS81Exit6Input
  exit10 : GS81Exit10Input
  exit11 : GS81Exit11Input
  gh74 : ClassicalInvolution.GH74SectionalModels
  ci : GSLit.ClassicalInvolutionInput
  rs : RestrictedStandardInput

theorem lemma81''
    (I : Lemma81Inputs'') :
    Lemma81StatementK :=
  lemma81'
    { in81 := I.in81
      cfi := I.cfi
      ac := I.ac
      aq := I.aq
      st := suzukiTausskyInput
      jo := I.jo
      f2 := I.f2
      l0 := I.l0
      conf := I.conf
      noNilp := I.noNilp
      fieldOrd := I.fieldOrd
      diag := I.diag
      step3 := I.step3
      step9 := gs81Step9Input I.centPerfect I.nineCent I.sp4Three
      exit6 := I.exit6
      exit10 := I.exit10
      exit11 := I.exit11
      gh74 := I.gh74
      ci := I.ci
      rs := I.rs }

end CFSG.ComponentClassification.GSThmB
