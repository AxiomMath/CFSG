module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermK1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineMain
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate4120

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporRu

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint.NativeSporadic
  CFSG.QuasithinUnique.A5.Kc3SporLine CFSG.QuasithinUnique.A5.Kc3SporPerm
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_facts' : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts

theorem ru_ta : (tab ruData.n (a ruData)).toArray = ruTa := by
  have : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a ru_facts'.toBaseFacts)]
    simp [ruTa]
  rw [this, Array.toArray_toList]

theorem ru_tb : (tab ruData.n (b ruData)).toArray = ruTb := by
  have : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b ru_facts'.toBaseFacts)]
    simp [ruTb]
  rw [this, Array.toArray_toList]

theorem ru_card : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv ru_facts'.toBaseFacts).toEquiv).symm.trans
      CFSG.Sporadic.Ru.card_Ru
  rw [hcard0]
  norm_num

instance
    : Finite (J ruData) := Nat.finite_of_card_ne_zero (by rw [ru_card]; norm_num)

theorem ru_cert' :
    BaseCertS ruData.n ruB
    (slpTabsA (tab ruData.n (a ruData)).toArray (tab ruData.n (b ruData)).toArray ruProg) ruQp
    154 187 191 189 193 ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 := by
  rw [ru_ta, ru_tb]
  have : slpTabsA ruTa ruTb ruProg = ruSLP := by simp [ruSLP]
  rw [this]
  exact ru_cert

theorem ru_data :
    genTabs ruData.n ruSg = ruQp.map (fun p =>
      (slpTabsA (tab ruData.n (a ruData)).toArray (tab ruData.n (b ruData)).toArray
        ruProg)[p.1]!) ∧
    genTabsInv ruData.n ruSg = ruQp.map (fun p =>
      (slpTabsA (tab ruData.n (a ruData)).toArray (tab ruData.n (b ruData)).toArray
        ruProg)[p.2]!) ∧
    BaseEnumOK ruData.n ruB (genTabs ruData.n ruSg) (genTabsInv ruData.n ruSg) ruEnum.1
      ruEnum.2.1 ruEnum.2.2 ∧ Nat.card ruR = 2 ^ 14 :=
  baseCertS_data (Γ := J ruData) (n := ruData.n) ruB (base_lt ru_facts')
    (base_property ru_facts') (a ruData) (b ruData) ruProg ru_valid ruQp 154 187 191 189 193
    ruEnum.1 ruEnum.2.1 ruEnum.2.2 14 ru_cert'

theorem ru_R_card :
    Nat.card ruR = 2 ^ 14 := ru_data.2.2.2

theorem ruR_isPGroup :
    IsPGroup 2 ruR := IsPGroup.of_card ru_R_card

theorem ruR_index :
    ¬ 2 ∣ ruR.index := by
  have h1 := Subgroup.card_mul_index ruR
  rw [ru_R_card, ru_card] at h1
  have h2 : ruR.index = 8906625 := by omega
  rw [h2]
  norm_num

theorem ru_hall
    : ∀ E : Subgroup (J ruData), E ≤ ruR → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
    (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → ¬ PairFibersAllowed (Fin ruPD.n) E :=
  Certificates.certificate4120 ru_ta ru_tb (base_property ru_facts')

theorem kc3LocalFor_ru :
    Kc3LocalFor (Kc3Spor .Ru) := by
  have hno := noDelta5Norm_of_sylow (Fin ruPD.n) ruR_isPGroup ruR_index ru_hall
  refine kc3LocalFor_of_noDelta5Norm (Γ := J ruData) ?_ hno
  intro X _ ⟨e⟩
  exact ⟨e.trans (seedEquiv ru_facts'.toBaseFacts)⟩

theorem kc3For_ru :
    Kc3For (Kc3Spor .Ru) :=
  kc3For_of_localFor (isoInv_spor .Ru) kc3LocalFor_ru

end CFSG.QuasithinUnique.A5.Kc3SporRu
