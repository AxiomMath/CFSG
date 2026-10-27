module

public import Certificates.Certificate3911

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split.Minus

open CFSG.EvenSmallLie.OmegaEight.Stage2

noncomputable def wit : MinusW.Wit :=
  Classical.choose Certificates.certificate3911

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
@[expose] noncomputable def sEnum3W : Enum := wit.sE3
@[expose] noncomputable def mEnum3W : Enum := wit.mE3

theorem wit_spec :
    MinusW.cCheck wit = true ∧ MinusW.tcCheck wit = true ∧ MinusW.ukCheck wit = true ∧
      MinusW.m2Check wit = true ∧ MinusW.offCheck wit = true ∧ MinusW.phiCheck wit = true ∧
      MinusW.c2Check wit = true ∧ MinusW.p3Check wit = true ∧ MinusW.candChk wit = true ∧
      MinusW.brayChk2 wit = true ∧ MinusW.sChk0 wit = true ∧ MinusW.tauChk0 wit = true ∧
      x0Chk = true ∧ MinusW.s2Chk wit = true ∧ MinusW.sChk1 wit = true ∧
      MinusW.tauChk1 wit = true ∧ zChk = true ∧ MinusW.noChk wit = true ∧
      MinusW.sChk3 wit = true ∧ MinusW.thirdChk wit = true ∧ MinusW.ncChk wit = true :=
  Classical.choose_spec Certificates.certificate3911

theorem c_check : MinusW.cCheck wit = true := wit_spec.1

theorem tc_check : MinusW.tcCheck wit = true := wit_spec.2.1

theorem uk_check : MinusW.ukCheck wit = true := wit_spec.2.2.1

theorem m2_check : MinusW.m2Check wit = true :=
  wit_spec.2.2.2.1

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

theorem bray_check2 : MinusW.brayChk2 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.1

theorem s_check0 : MinusW.sChk0 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.1

theorem tau_check0 : MinusW.tauChk0 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.1

theorem x0_check : x0Chk = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s2_check : MinusW.s2Chk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_check1 : MinusW.sChk1 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tau_check1 : MinusW.tauChk1 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem z_check : zChk = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem no_check : MinusW.noChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s_check3 : MinusW.sChk3 wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem third_check : MinusW.thirdChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem nc_check : MinusW.ncChk wit = true :=
  wit_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.N3Split.Minus
