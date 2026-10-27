module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineK1

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporHe

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.He CFSG.Blueprint.NativeSporadic
  CFSG.QuasithinUnique.A5.Kc3SporLine CFSG.QuasithinUnique.A5.Kc3J

noncomputable def heSg : List J :=
  heQp.map fun p => (slpElts a b heProg).getD p.1 1

noncomputable def heR : Subgroup J := Subgroup.closure {x | x ∈ heSg}

theorem he_ta : (tab 8330 (a : J)).toArray = heTa := by
  have : tab 8330 (a : J) = heTa.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (a : J) rep_alpha]
    simp [heTa, orb]
  rw [this, Array.toArray_toList]

theorem he_tb : (tab 8330 (b : J)).toArray = heTb := by
  have : tab 8330 (b : J) = heTb.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (b : J) rep_beta]
    simp [heTb, orb]
  rw [this, Array.toArray_toList]

theorem he_card : Nat.card J = 2 ^ 10 * 3935925 := by
  rw [card_J]; norm_num

theorem he_cert' : BaseCertS 8330 heB
    (slpTabsA (tab 8330 (a : J)).toArray (tab 8330 (b : J)).toArray heProg) heQp
    170 249 253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2 10 := by
  rw [he_ta, he_tb]
  have : slpTabsA heTa heTb heProg = heSLP := by simp [heSLP]
  rw [this]
  exact he_cert

theorem he_sGens :
    genTabs 8330 heSg = heQp.map (fun p => heSLP[p.1]!) ∧ Nat.card heR = 2 ^ 10 := by
  have := sGens_of_baseCertS' (n := 8330) heB he_base_lt he_base_property a b heProg he_valid heQp
    170 249 253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2 10 he_cert'
  refine ⟨?_, this.2⟩
  rw [heSg, this.1, he_ta, he_tb]
  have : slpTabsA heTa heTb heProg = heSLP := by simp [heSLP]
  rw [this]

theorem heR_isPGroup :
    IsPGroup 2 heR := IsPGroup.of_card he_sGens.2

theorem heR_index :
    ¬ 2 ∣ heR.index := by
  have h1 := Subgroup.card_mul_index heR
  rw [he_sGens.2, he_card] at h1
  have h2 : heR.index = 3935925 := by omega
  rw [h2]
  norm_num

theorem kc3For_he_of_sylow
    {R : Subgroup J} (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.index)
    (hall : ∀ E : Subgroup J, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → ¬ PairFibersAllowed (Fin 8330) E) :
    CFSG.QuasithinUnique.A5.Kc3For (CFSG.QuasithinUnique.A5.Kc3Spor .He) := by
  have hno := noDelta5Norm_of_sylow (Fin 8330) hR hRi hall
  refine CFSG.QuasithinUnique.A5.kc3For_of_localFor (CFSG.QuasithinUnique.A5.isoInv_spor .He)
    (kc3LocalFor_of_noDelta5Norm (Γ := J) ?_ hno)
  intro X _ ⟨e⟩
  exact ⟨e.trans heEquivJ⟩

theorem kc3For_he_of_hall
    (hall : ∀ E : Subgroup J, E ≤ heR → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → ¬ PairFibersAllowed (Fin 8330) E) :
    CFSG.QuasithinUnique.A5.Kc3For (CFSG.QuasithinUnique.A5.Kc3Spor .He) :=
  kc3For_he_of_sylow heR_isPGroup heR_index hall

end CFSG.QuasithinUnique.A5.Kc3SporHe
