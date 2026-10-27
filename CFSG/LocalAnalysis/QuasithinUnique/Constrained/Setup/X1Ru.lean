module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RowCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuCheck
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_charPair :
    ∃ R : Subgroup (J ruData), IsPGroup 2 R ∧ ¬ 2 ∣ R.index ∧ CharPair (J ruData) R := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have : FaithfulSMul (J ruData) (Fin ruData.n) := faithful hF.toBaseFacts
  have ha : tab ruData.n (a ruData) = ruTa'.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a hF.toBaseFacts)]
    simp [ruTa']
  have hb : tab ruData.n (b ruData) = ruTb'.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b hF.toBaseFacts)]
    simp [ruTb']
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hcard : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
    rw [hcard0]; norm_num
  exact charPair_of_rowChecks (n := ruData.n) (base_lt hF) (base_property hF) (a ruData)
    (b ruData) (closure_ab ruData) (by rw [ha, Array.toArray_toList])
    (by rw [hb, Array.toArray_toList]) ru_progValid ruNT2 rfl ru_qpOK ruEnum2.1 ruEnum2.2.1
    ruEnum2.2.2 ru_enumOK hcard (by decide) ru_enum_size ruGens2 rfl ruP rfl ruNodes1 ruNodes2
    ruNodes3 ru_nodes.1 ru_nodes.2.1 ru_nodes.2.2 ruL1 ruL2 ruL3 rfl rfl rfl ru_c1 ru_c2 ru_c3
    ru_bounds.1 ru_bounds.2.1 ru_bounds.2.2.1 ru_bounds.2.2.2.1 ru_gg ru_hh ru_normZ1 ru_normZ3
    ru_notNormZ3 ru_notNormZ1 ru_wprogValid ruWNT rfl ru_bounds.2.2.2.2.1 ru_bounds.2.2.2.2.2
    ru_wa ru_wb

theorem twoExtensionFor_Ru :
    TwoExtensionFor .Ru := by
  obtain ⟨R, hRp, hRi, hmodel⟩ := ru_charPair
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  intro X _ _ T K hK hT hTi hKT ⟨e⟩
  have : K.Normal := hK
  exact @twoExtension_of_charPair_of_equiv (J ruData) (NativeSporadic.Carrier .Ru) inferInstance
    inferInstance inferInstance (seedEquiv hF.toBaseFacts).symm R hRp hRi hmodel X inferInstance
    inferInstance T K inferInstance hT hTi hKT e

end CFSG.QuasithinUnique.Setup.X1
