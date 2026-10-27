module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Pipe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Tab

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.J2 CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint

theorem j2_twoMaxOver
    : ∃ R : Subgroup J, IsPGroup 2 R ∧ ¬ 2 ∣ R.index ∧ TwoMaxOver J R := by
  have hta : j2Data.ta = (tab 315 (a : J)).toArray := by
    rw [j2_tab_a, ← j2_ta_eq, Array.toArray_toList]
  have htb : j2Data.tb = (tab 315 (b : J)).toArray := by
    rw [j2_tab_b, ← j2_tb_eq, Array.toArray_toList]
  exact pipeline_twoMaxOver (n := 315) (by norm_num) a b closure_ab hta htb (k := 7) (m := 4725)
    (by rw [card_J]; norm_num) (by decide) rfl j2_invValid j2_slpValid j2_qpOK j2Enum.1
    j2Enum.2.1 j2Enum.2.2 j2_enumOK (by rw [j2_enum_size]; norm_num) j2_treeValid j2_edgeOK
    j2_aszOK j2_xsOK j2ROm rfl j2_blocksClosed j2_repsOK j2_closureOK j2_shapeOK

theorem twoExtensionFor_J2
    : TwoExtensionFor .J2 := by
  obtain ⟨R, hRp, hRi, hmodel⟩ := j2_twoMaxOver
  intro X _ _ T K hK hT hTi hKT ⟨e⟩
  have : K.Normal := hK
  exact @twoExtension_of_model_of_equiv ↥J (NativeSporadic.Carrier .J2) inferInstance inferInstance
    inferInstance (CFSG.Sporadic.Bridge.J2.nativeEquiv.symm) R hRp hRi hmodel X inferInstance
    inferInstance T K inferInstance hT hTi hKT e

end CFSG.QuasithinUnique.Setup.X1
