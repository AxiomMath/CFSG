module

public import Certificates.Certificate3411

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2.Minus

noncomputable def wit : MinusW.Wit :=
  Classical.choose Certificates.certificate3411

@[expose] noncomputable def cEnumW : Enum := wit.cE
@[expose] noncomputable def tcEnumW : Enum := wit.tcE
@[expose] noncomputable def uEnumW : Enum := wit.uE
@[expose] noncomputable def c2EnumW : Enum := wit.c2E
@[expose] noncomputable def p3EnumW : Enum := wit.p3E

theorem wit_spec :
    MinusW.cCheck wit = true ∧ MinusW.tcCheck wit = true ∧ MinusW.uCheck wit = true ∧
      MinusW.m2Check wit = true ∧ MinusW.offCheck wit = true ∧ MinusW.phiCheck wit = true ∧
      MinusW.c2Check wit = true ∧ MinusW.p3Check wit = true ∧ MinusW.candChk wit = true ∧
      MinusW.brayChk wit 2 brayProg2 brayOut2 = true ∧
      MinusW.brayChk wit 3 brayProg3 brayOut3 = true ∧
      MinusW.brayChk wit 4 brayProg4 brayOut4 = true ∧
      MinusW.brayChk wit 5 brayProg5 brayOut5 = true ∧
      MinusW.brayChk wit 6 brayProg6 brayOut6 = true ∧
      MinusW.sChk0 wit = true ∧ MinusW.sChk1 wit = true ∧ MinusW.secondChk wit = true ∧
      MinusW.no8Chk wit = true :=
  Classical.choose_spec Certificates.certificate3411

theorem c_check : MinusW.cCheck wit = true := wit_spec.1

theorem tc_check : MinusW.tcCheck wit = true := wit_spec.2.1

theorem u_check : MinusW.uCheck wit = true := wit_spec.2.2.1

theorem m2_check : MinusW.m2Check wit = true := wit_spec.2.2.2.1

theorem off_check : MinusW.offCheck wit = true :=
  wit_spec.2.2.2.2.1

theorem phi_check : MinusW.phiCheck wit = true :=
  wit_spec.2.2.2.2.2.1

theorem c2_check : MinusW.c2Check wit = true :=
  wit_spec.2.2.2.2.2.2.1

theorem p3_check : MinusW.p3Check wit = true :=
  wit_spec.2.2.2.2.2.2.2.1

theorem cand_check : MinusW.candChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.1

theorem bray_check2 :
    MinusW.brayChk wit 2 brayProg2 brayOut2 = true := wit_spec.2.2.2.2.2.2.2.2.2.1

theorem bray_check3 :
    MinusW.brayChk wit 3 brayProg3 brayOut3 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.1

theorem bray_check4 :
    MinusW.brayChk wit 4 brayProg4 brayOut4 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.2.1

theorem bray_check5 :
    MinusW.brayChk wit 5 brayProg5 brayOut5 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bray_check6 :
    MinusW.brayChk wit 6 brayProg6 brayOut6 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_check0 : MinusW.sChk0 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_check1 : MinusW.sChk1 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem second_check : MinusW.secondChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem no8_check : MinusW.no8Chk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.Stage2.Minus
