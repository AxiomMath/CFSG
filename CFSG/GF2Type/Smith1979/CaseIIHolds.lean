module

public import CFSG.GF2Type.Smith1979.CaseIIAssembly
public import CFSG.GF2Type.Smith1979.CaseIIExclU43
public import CFSG.GF2Type.Smith1979.CaseIIRderR2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case2

theorem u43Frob56Free_holds : U43Frob56Free :=
  fun hX _ hy S hS2 hS8 hyS hfpf => false_of_psu43_frob56 hX hy S hS2 hS8 hyS hfpf

theorem rderFacts_holds : RderFacts :=
  fun D hCE => ⟨exists_seven_Rder D hCE, exists_six_Rder D hCE,
    fun _ hy _ hs => conj_mem_Sbar D hCE hy hs⟩

end Case2

theorem caseIIStmt_holds : CaseIIStmt :=
  caseIIStmt_of_inputs Case2.u43Frob56Free_holds Case2.rderFacts_holds

end CFSG.GF2Type.Smith1979
