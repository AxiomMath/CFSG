module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSCheck
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_charPair :
    ∃ R : Subgroup (J hsData), IsPGroup 2 R ∧ ¬ 2 ∣ R.index ∧ CharPair (J hsData) R := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  have : FaithfulSMul (J hsData) (Fin hsData.n) := faithful hF.toBaseFacts
  have ha : tab hsData.n (a hsData) = hsTa'.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (a hsData) (rep_a hF.toBaseFacts)]
    simp [hsTa']
  have hb : tab hsData.n (b hsData) = hsTb'.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (b hsData) (rep_b hF.toBaseFacts)]
    simp [hsTb']
  have hcard0 : Nat.card (J hsData) = 44352000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.HS.card_HS
  have hcard : Nat.card (J hsData) = 2 ^ 9 * 86625 := by
    rw [hcard0]; norm_num
  exact charPair_of_checks (n := hsData.n) (a hsData) (b hsData) (closure_ab hsData)
    (by rw [ha, Array.toArray_toList]) (by rw [hb, Array.toArray_toList]) hs_progValid hsNT2 rfl
    hs_qpOK hsEnum2.1 hsEnum2.2.1 hsEnum2.2.2 hs_enumOK hcard (by decide) hs_enum_size hsRl rfl
    hsGens2 rfl hsZ1 hsQc rfl rfl hs_bounds.1 hs_bounds.2.1 hs_bounds.2.2.1 hs_bounds.2.2.2.1
    hs_gg hs_hh hs_normZ1 hs_normQc hs_notNormQc hs_notNormZ1 hs_wprogValid hsWNT rfl
    hs_bounds.2.2.2.2.1 hs_bounds.2.2.2.2.2 hs_wa hs_wb

theorem twoExtensionFor_HS :
    TwoExtensionFor .HS := by
  obtain ⟨R, hRp, hRi, hmodel⟩ := hs_charPair
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  intro X _ _ T K hK hT hTi hKT ⟨e⟩
  have : K.Normal := hK
  exact @twoExtension_of_charPair_of_equiv (J hsData) (NativeSporadic.Carrier .HS) inferInstance
    inferInstance inferInstance (seedEquiv hF.toBaseFacts).symm R hRp hRi hmodel X inferInstance
    inferInstance T K inferInstance hT hTi hKT e

end CFSG.QuasithinUnique.Setup.X1
