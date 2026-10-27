module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOddCentre
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBL2Reduction
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOEvenLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBL4U4

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancingLocal


theorem false_of_E7S (hE7 : BurgoynePropBE7S) {J : Type} [Group J] [Finite J] {K : Subgroup J}
    [K.Normal] {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K} (hH : PropBHyp J K t Y c)
    {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (B.rhoZ K).range) .E7 n p f) : False := by
  obtain ⟨v, hv2, R, hRv, hRc, p₁, n₁, hp₁, hp₁2, hn₁, N, hN, hNodd, he⟩ :=
    B.exists_L2_component_of_propBHyp K hH
  have : Finite (GeneralizedFitting.subgroup (B.rhoZ K).range) := inferInstance
  exact hE7 _ n p f hp2 hL v hv2 R hRv hRc p₁ n₁ hp₁2 hn₁ N hNodd he

theorem false_of_classicalS (hcl : BurgoynePropBClassicalS) {J : Type} [Group J] [Finite J]
    {K : Subgroup J} [K.Normal] {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K}
    (hH : PropBHyp J K t Y c) {τ : StatedLieTag} {n p f : ℕ}
    (hτ : ((τ = .PSL ∨ τ = .PSU) ∧ 6 ≤ n ∧ Even n) ∨ (τ = .PSp ∧ 3 ≤ n)) (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup (B.rhoZ K).range) τ n p f) : False := by
  obtain ⟨v, hv2, R, hRv, hRc, p₁, n₁, hp₁, hp₁2, hn₁, N, hN, hNodd, he⟩ :=
    B.exists_L2_component_of_propBHyp K hH
  have : Finite (GeneralizedFitting.subgroup (B.rhoZ K).range) := inferInstance
  exact hcl _ τ n p f hτ hp2 hL v hv2 R hRv hRc p₁ n₁ hp₁2 hn₁ N hNodd he

theorem burgoynePropB_of_inputs (hGA : GriessMultipliersAllModels)
    (hE7 : BurgoynePropBE7S) (hcl : BurgoynePropBClassicalS)
    (hklein : BurgoynePropBSpinPlusKleinInput) (hexc : BurgoynePropBDrExcInput)
    (hD4 : BurgoynePropBPlusFourInput) : BurgoynePropB := by
  intro J _ _ K _ hq hM4 t s ht hs2 Y hY hYO hst hsy Q hQs hQc hQiso c hcZ hcQ hc2 hprop
  have hY' : Y.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict ≠ ⊥ :=
    fun h => hY (by
      rw [← MonoidHom.subtype_comp_rangeRestrict
        (conjQuotAction K (centralPreimage (pPrimeCore 2 K))), ← Subgroup.map_map, h,
        Subgroup.map_bot])
  have hH : PropBHyp J K t Y c :=
    ⟨hq, hM4, ht, hY', hYO, s, hs2, hst, hsy, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, hprop⟩
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hL⟩ := hM4.2.2.1
  cases τ with
  | PSL =>
    have hn : 2 ≤ n := hadm.2.2.1
    rcases Nat.even_or_odd n with hev | hodd
    · rcases (by obtain ⟨k, hk⟩ := hev; omega : n = 2 ∨ n = 4 ∨ 6 ≤ n) with rfl | rfl | h6
      · exact (hM4.2.2.2.1 p f hp hp2 hL).elim
      · exact B.burgoynePropB_PSL4_uncond K hH hp2 hL
      · exact (false_of_classicalS hcl hH (Or.inl ⟨Or.inl rfl, h6, hev⟩) hp2 hL).elim
    · exact (B.false_of_PSL_odd K hH hp2 hodd hL).elim
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    rcases Nat.even_or_odd n with hev | hodd
    · rcases (by obtain ⟨k, hk⟩ := hev; omega : n = 4 ∨ 6 ≤ n) with rfl | h6
      · exact B.burgoynePropB_PSU4_uncond K hH hp2 hL
      · exact (false_of_classicalS hcl hH (Or.inl ⟨Or.inr rfl, h6, hev⟩) hp2 hL).elim
    · exact (B.false_of_PSU_odd K hH hp2 hodd hL).elim
  | PSp =>
    have hn : 2 ≤ n := hadm.2.2.1
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | h3
    · exact B.burgoynePropB_PSp4 K hq hM4 hp2 hL ht hY' hYO hcZ hc2
    · exact (false_of_classicalS hcl hH (Or.inr ⟨rfl, h3⟩) hp2 hL).elim
  | POmegaOdd => exact B.burgoynePropB_POmegaOdd K hH hp2 hL
  | POmegaMinus => exact B.burgoynePropB_POmegaMinus K hexc hH hp2 hL
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    rcases (by omega : n = 4 ∨ 5 ≤ n) with rfl | h5
    · exact hD4 J K t Y c hH p f hp2 hL
    · exact B.burgoynePropB_POmegaPlus K hklein hexc hH hp2 h5 hL
  | G2 => exact (B.false_of_adjoint K hH (Or.inl rfl) hp2 hL).elim
  | F4 => exact (B.false_of_adjoint K hH (Or.inr (Or.inl rfl)) hp2 hL).elim
  | E8 => exact (B.false_of_adjoint K hH (Or.inr (Or.inr rfl)) hp2 hL).elim
  | E6 => exact (B.false_of_E6 K hH hp2 hL).elim
  | E7 => exact (false_of_E7S hE7 hH hp2 hL).elim
  | twistedE6 => exact (B.false_of_twisted K hGA hH (Or.inl rfl) hp2 hL).elim
  | trialityD4 => exact (B.false_of_twisted K hGA hH (Or.inr (Or.inl rfl)) hp2 hL).elim
  | twistedG2 => exact (B.false_of_twisted K hGA hH (Or.inr (Or.inr rfl)) hp2 hL).elim
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

end CFSG.ComponentClassification.Burgoyne
