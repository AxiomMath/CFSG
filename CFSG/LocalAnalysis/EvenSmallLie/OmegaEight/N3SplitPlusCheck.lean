module

public import Certificates.Certificate3910

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split.Plus

open CFSG.EvenSmallLie.OmegaEight.Stage2

noncomputable def wit : PlusW.Wit :=
  Classical.choose Certificates.certificate3910

@[expose] noncomputable def cEnumW : Enum := wit.cE
@[expose] noncomputable def tcEnumW : Enum := wit.tcE
@[expose] noncomputable def ukEnumW : Enum := wit.ukE
@[expose] noncomputable def c2EnumW : Enum := wit.c2E
@[expose] noncomputable def p3EnumW : Enum := wit.p3E
@[expose] noncomputable def sEnum0W : Enum := wit.sE0
@[expose] noncomputable def mEnum0W : Enum := wit.mE0
@[expose] noncomputable def s2EnumW : Enum := wit.s2E
@[expose] noncomputable def m2EnumW : Enum := wit.m2E
@[expose] noncomputable def sEnum1W : Enum := wit.sE1
@[expose] noncomputable def mEnum1W : Enum := wit.mE1

theorem wit_spec :
    PlusW.cCheck wit = true ∧ PlusW.tcCheck wit = true ∧ PlusW.ukCheck wit = true ∧
      PlusW.m2Check wit = true ∧ PlusW.offCheck wit = true ∧ PlusW.phiCheck wit = true ∧
      PlusW.c2Check wit = true ∧ PlusW.p3Check wit = true ∧ PlusW.candChk wit = true ∧
      PlusW.brayChk wit 2 brayProg2 brayOut2 = true ∧
      PlusW.brayChk wit 3 brayProg3 brayOut3 = true ∧
      PlusW.sChk0 wit = true ∧ PlusW.tauChk0 wit = true ∧ x0Chk = true ∧
      PlusW.s2Chk wit = true ∧ PlusW.sChk1 wit = true ∧ PlusW.tauChk1 wit = true ∧
      zChk = true ∧ PlusW.noChk wit = true ∧ PlusW.ncChk wit = true :=
  Classical.choose_spec Certificates.certificate3910

theorem c_check : PlusW.cCheck wit = true := wit_spec.1

theorem tc_check : PlusW.tcCheck wit = true := wit_spec.2.1

theorem uk_check : PlusW.ukCheck wit = true := wit_spec.2.2.1

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

theorem bray_check2 :
    PlusW.brayChk wit 2 brayProg2 brayOut2 = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.1

theorem bray_check3 :
    PlusW.brayChk wit 3 brayProg3 brayOut3 = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.1

theorem s_check0 : PlusW.sChk0 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.1

theorem tau_check0 : PlusW.tauChk0 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem x0_check : x0Chk = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s2_check : PlusW.s2Chk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_check1 : PlusW.sChk1 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tau_check1 : PlusW.tauChk1 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem z_check : zChk = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem no_check : PlusW.noChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem nc_check : PlusW.ncChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.N3Split.Plus
