module

public import Certificates.Certificate3410

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2.Plus

noncomputable def wit : PlusW.Wit :=
  Classical.choose Certificates.certificate3410

@[expose] noncomputable def cEnumW : Enum := wit.cE
@[expose] noncomputable def tcEnumW : Enum := wit.tcE
@[expose] noncomputable def uEnumW : Enum := wit.uE
@[expose] noncomputable def c2EnumW : Enum := wit.c2E
@[expose] noncomputable def p3EnumW : Enum := wit.p3E

theorem wit_spec :
    PlusW.cCheck wit = true ∧ PlusW.tcCheck wit = true ∧ PlusW.uCheck wit = true ∧
      PlusW.m2Check wit = true ∧ PlusW.offCheck wit = true ∧ PlusW.phiCheck wit = true ∧
      PlusW.c2Check wit = true ∧ PlusW.p3Check wit = true ∧ PlusW.candChk wit = true ∧
      PlusW.brayChk wit 0 brayProg0 brayOut0 = true ∧
      PlusW.brayChk wit 1 brayProg1 brayOut1 = true ∧
      PlusW.brayChk wit 2 brayProg2 brayOut2 = true ∧
      PlusW.brayChk wit 3 brayProg3 brayOut3 = true ∧
      PlusW.brayChk wit 6 brayProg6 brayOut6 = true ∧
      PlusW.brayChk wit 7 brayProg7 brayOut7 = true ∧
      PlusW.sChk4 wit = true ∧ PlusW.sChk5 wit = true :=
  Classical.choose_spec Certificates.certificate3410

theorem c_check : PlusW.cCheck wit = true := wit_spec.1

theorem tc_check : PlusW.tcCheck wit = true := wit_spec.2.1

theorem u_check : PlusW.uCheck wit = true := wit_spec.2.2.1

theorem m2_check : PlusW.m2Check wit = true := wit_spec.2.2.2.1

theorem off_check : PlusW.offCheck wit = true :=
  wit_spec.2.2.2.2.1

theorem phi_check : PlusW.phiCheck wit = true :=
  wit_spec.2.2.2.2.2.1

theorem c2_check : PlusW.c2Check wit = true :=
  wit_spec.2.2.2.2.2.2.1

theorem p3_check : PlusW.p3Check wit = true :=
  wit_spec.2.2.2.2.2.2.2.1

theorem cand_check : PlusW.candChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.1

theorem bray_check0 :
    PlusW.brayChk wit 0 brayProg0 brayOut0 = true := wit_spec.2.2.2.2.2.2.2.2.2.1

theorem bray_check1 :
    PlusW.brayChk wit 1 brayProg1 brayOut1 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.1

theorem bray_check2 :
    PlusW.brayChk wit 2 brayProg2 brayOut2 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.2.1

theorem bray_check3 :
    PlusW.brayChk wit 3 brayProg3 brayOut3 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bray_check6 :
    PlusW.brayChk wit 6 brayProg6 brayOut6 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bray_check7 :
    PlusW.brayChk wit 7 brayProg7 brayOut7 = true := wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_check4 : PlusW.sChk4 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_check5 : PlusW.sChk5 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.Stage2.Plus
