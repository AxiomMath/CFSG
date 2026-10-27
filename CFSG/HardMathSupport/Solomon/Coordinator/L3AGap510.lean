module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem glaPPrimeCore_eq_bot_of_quasisimple {S : Type*} [Group S] [Finite S]
    (hq : CFSG.Open.IsQuasisimple S) (hz : ∀ z : S, z ∈ Subgroup.center S → z ^ 3 = 1)
    (h3 : 3 ∣ Nat.card S) : GLAPPrimeCore 3 S = ⊥ := by
  have hcop := coprime_card_gLAPPrimeCore_aux 3 S
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    (GLAPPrimeCore 3 S) with h | h
  · rw [eq_bot_iff]
    intro n hn
    have h1 : n ^ 3 = 1 := hz n (h hn)
    have h2 : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    have h3' : orderOf n ∣ Nat.card (GLAPPrimeCore 3 S) :=
      Subgroup.orderOf_dvd_natCard (GLAPPrimeCore 3 S) hn
    have h4 : Nat.Coprime (orderOf n) 3 := (Nat.Coprime.coprime_dvd_left h3' hcop.symm)
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h2))
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) h3) (by norm_num)

theorem fixData_of_type {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hT : IsExtremalType Y ∨ IsSLThreeEps Y) {α : MulAut Y} (h3 : α ^ 3 = 1)
    (hf : IsFieldAutThree α) : FixData Y α := by
  rcases model_of_type hY hT with ⟨π, p, f, K, _, hK, hq, h8, h2, ⟨e⟩⟩ |
      ⟨π, p, f, K, _, hK, hq, h8, h2, ⟨e⟩⟩
  · exact fixData_cover hY hK hq h8 h2 e h3 hf
  · exact fixData_proj hY hK hq h8 h2 e h3 hf

theorem layer_of_fixData {Y : Type} [Group Y] [Finite Y] {α : MulAut Y} (h : FixData Y α) :
    ∃ S : Subgroup Y, (∀ J : Subgroup Y, GLAPComponent 3 (fixSub α) J ↔ J = S) ∧
      GLAPLayer 3 (fixSub α) = S ∧ CFSG.Open.IsQuasisimple ↥S ∧ IsL3Type ↥S ∧
      GLAPPrimeCore 3 ↥S = ⊥ ∧ (∀ z : ↥S, z ∈ Subgroup.center ↥S → (z : Y) ∈ Subgroup.center Y) ∧
      Subgroup.center Y ≤ S := by
  obtain ⟨S, hSF, hcomm, hpow, hqS, hty, hz3, h3d, hcen, hZS, -⟩ := h
  have hO := glaPPrimeCore_eq_bot_of_quasisimple hqS hz3 h3d
  obtain ⟨-, comp, layer⟩ := layer_of_normal_quasisimple hSF hcomm hpow hqS hO
  exact ⟨S, comp, layer, hqS, hty, hO, hcen, hZS⟩

theorem gap510_Nontrivial_holds : LocalBalance.Lemma510Ns.Gap510_Nontrivial := by
  intro Y _ _ hq hT α h3 hf
  obtain ⟨S, -, hl, hqS, -⟩ := layer_of_fixData (fixData_of_type hq hT h3 hf)
  rw [hl]
  intro h
  have := CFSG.ComponentClassification.Quasisimple.nontrivial hqS
  exact (Subgroup.nontrivial_iff_ne_bot _).1 this h

noncomputable def barEquivOfCore {Y : Type} [Group Y] {S : Subgroup Y}
    (hO : GLAPPrimeCore 3 ↥S = ⊥) : ↥S ≃* barOf 3 S :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)

theorem barEquivOfCore_apply {Y : Type} [Group Y] {S : Subgroup Y} (hO : GLAPPrimeCore 3 ↥S = ⊥)
    (y : ↥S) : barEquivOfCore hO y = QuotientGroup.mk' (GLAPPrimeCore 3 ↥S) y := by
  unfold barEquivOfCore
  rw [MulEquiv.trans_apply]
  have : (QuotientGroup.quotientBot.symm : ↥S ≃* ↥S ⧸ (⊥ : Subgroup ↥S)) y =
      (y : ↥S ⧸ (⊥ : Subgroup ↥S)) := rfl
  rw [this, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem gap510_Type_holds : LocalBalance.Lemma510Ns.Gap510_Type := by
  intro Y _ _ hq hT α h3 hf J hJ
  obtain ⟨S, comp, -, -, hty, hO, -⟩ := layer_of_fixData (fixData_of_type hq hT h3 hf)
  rw [(comp J).1 hJ]
  exact isL3Type_of_mulEquiv (barEquivOfCore hO) hty

theorem gap510_Centre_holds : LocalBalance.Lemma510Ns.Gap510_Centre := by
  intro Y _ _ hq hT α h3 hf J hJ
  obtain ⟨S, comp, -, hqS, -, hO, hcen, hZS⟩ := layer_of_fixData (fixData_of_type hq hT h3 hf)
  rw [(comp J).1 hJ]
  refine ⟨hZS, ?_⟩
  rintro y ⟨-, ⟨y', hy', rfl⟩⟩
  let e := barEquivOfCore hO
  have hQ : CFSG.Open.IsQuasisimple (barOf 3 S) := isQuasisimple_open_of_mulEquiv e.symm hqS
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥S) y' ∈ Subgroup.center (barOf 3 S) :=
    pCore_le_center Nat.prime_three hQ hy'
  have h2 : y' ∈ Subgroup.center ↥S := by
    have := mem_center_of_mulEquiv e.symm h1
    have h3 : e.symm (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S) y') = y' := by
      rw [MulEquiv.symm_apply_eq]
      exact (barEquivOfCore_apply hO y').symm
    rwa [h3] at this
  exact hcen y' h2

theorem inputSL3FieldFixed_holds : LocalBalance.Lemma512Ns.InputSL3FieldFixed := by
  intro Y _ _ hq hT hz α h3 hf
  obtain ⟨S, -, -, -, hqS, -, -, -, -, -, hex⟩ := fixData_of_type hq hT h3 hf
  obtain ⟨hFS, hAny⟩ := hex hz
  have h1 : LocalBalance.Lemma512Ns.fixedSub α = S := hFS
  rw [h1]
  exact ⟨hqS, hAny⟩

end CFSG.HardMathSupport.Solomon.Coordinator
