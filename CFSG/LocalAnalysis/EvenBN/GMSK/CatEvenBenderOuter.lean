module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuterFixed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace CatEvenBender

@[expose] def EvenOuterListOf (C R : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ D : Subgroup (fixedSubgroup σ), IsComponent D → C (D ⧸ center D) → R S

@[expose] def EvenOuterFamilyOf (C R : (X : Type) → [Group X] → Prop) (τ : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ m e : ℕ, StatedLieAdmissible τ m 2 e → LieModel S τ m 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ D : Subgroup (fixedSubgroup σ), IsComponent D → C (D ⧸ center D) → R S

theorem evenOuterListOf_of_families {C R : (X : Type) → [Group X] → Prop}
    (h : ∀ τ, EvenOuterFamilyOf C R τ) : EvenOuterListOf C R := by
  intro S _ _ hS hna heven σ hσ hout D hD hC
  obtain ⟨τ, m, e, hadm, hmS⟩ := heven
  exact h τ S hS hna m e hadm hmS σ hσ hout D hD hC

theorem evenOuterFamilyOf_of_not_admissible {C R : (X : Type) → [Group X] → Prop}
    {τ : StatedLieTag} (hτ : ∀ m e : ℕ, ¬ StatedLieAdmissible τ m 2 e) :
    EvenOuterFamilyOf C R τ :=
  fun _ _ _ _ _ m e hadm => absurd hadm (hτ m e)

theorem evenOuterFamilyOf_of_involutions_inner {C R : (X : Type) → [Group X] → Prop}
    {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (m e : ℕ), StatedLieAdmissible τ m 2 e → LieModel K τ m 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) :
    EvenOuterFamilyOf C R τ := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout
  exact absurd (hτ S m e hadm hmS σ (hσ ▸ pow_orderOf_eq_one σ)) hout

theorem evenOuterFamilyOf_POmegaOdd {C R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf C R .POmegaOdd :=
  evenOuterFamilyOf_of_not_admissible fun _ _ hadm => hadm.2.2.2 rfl

theorem evenOuterFamilyOf_twistedG2 {C R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf C R .twistedG2 :=
  evenOuterFamilyOf_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

section SuzukiReeTits

theorem evenOuterFamilyOf_twistedB2 {C R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf C R .twistedB2 := by
  refine evenOuterFamilyOf_of_involutions_inner fun K _ m e _ hmK => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem evenOuterFamilyOf_twistedF4 {C R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf C R .twistedF4 := by
  refine evenOuterFamilyOf_of_involutions_inner fun K _ m e _ hmK => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem evenOuterFamilyOf_Tits {C R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf C R .Tits := by
  refine evenOuterFamilyOf_of_involutions_inner fun K _ m e hadm hmK => ?_
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem evenOuterListOf_of_open_families {C R : (X : Type) → [Group X] → Prop}
    (hPSL : EvenOuterFamilyOf C R .PSL) (hPSU : EvenOuterFamilyOf C R .PSU)
    (hPSp : EvenOuterFamilyOf C R .PSp) (hOp : EvenOuterFamilyOf C R .POmegaPlus)
    (hOm : EvenOuterFamilyOf C R .POmegaMinus) (hG2 : EvenOuterFamilyOf C R .G2)
    (hF4 : EvenOuterFamilyOf C R .F4) (hE6 : EvenOuterFamilyOf C R .E6)
    (hE7 : EvenOuterFamilyOf C R .E7) (hE8 : EvenOuterFamilyOf C R .E8)
    (h2E6 : EvenOuterFamilyOf C R .twistedE6) (h3D4 : EvenOuterFamilyOf C R .trialityD4) :
    EvenOuterListOf C R := by
  apply evenOuterListOf_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact evenOuterFamilyOf_POmegaOdd
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact evenOuterFamilyOf_twistedB2
  · exact evenOuterFamilyOf_twistedG2
  · exact evenOuterFamilyOf_twistedF4
  · exact evenOuterFamilyOf_Tits

end SuzukiReeTits

@[expose] def EvenTagDet (C : (X : Type) → [Group X] → Prop) (t₀ : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n g : ℕ), C X → StatedLieAdmissible t n 2 g →
    LieModel X t n 2 g → t = t₀

variable {C R : (X : Type) → [Group X] → Prop} {t₀ : StatedLieTag}

theorem EvenTagDet.tag_eq_of_simple (hdet : EvenTagDet C t₀) {D : Type} [Group D]
    (hq : IsQuasisimple D) (hs : IsSimpleGroup D) (hC : C (D ⧸ center D)) {t : StatedLieTag}
    {n g : ℕ} (hadm : StatedLieAdmissible t n 2 g) (hD : LieModel D t n 2 g) : t = t₀ :=
  hdet (D ⧸ center D) t n g hC hadm
    (SeitzReduction.LinearPilot.lieModel_quotient_center_of_center_eq_bot
      (SeitzReduction.F4Pilot.center_eq_bot_of_isQuasisimple hq hs) hD)

open CFSG.ComponentClassification in
theorem EvenTagDet.false_of_isComponent_statedSp (hdet : EvenTagDet C t₀)
    (ht₀ : t₀ = .PSU ∨ t₀ = .twistedB2)
    (h64 : ∀ (X : Type) [Group X], C X → 2 ^ 6 ∣ Nat.card X) {X : Type} [Group X]
    {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) (hC : C (D ⧸ center D)) :
    False := by
  have hg : 1 ≤ g := by
    by_contra h0
    have hk1 : Nat.card k = 1 := by rw [hk, show g = 0 by omega, pow_zero]
    exact absurd hk1 (ne_of_gt Finite.one_lt_card)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have hcardX : Nat.card X = Nat.card k ^ (r ^ 2) *
      ∏ j ∈ Finset.Icc 1 r, (Nat.card k ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv]
    exact LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r
  have hdvdX : 2 ^ 6 ∣ Nat.card X :=
    ((h64 _ hC).trans (card_quotient_dvd_card (center D))).trans
      (Subgroup.card_subgroup_dvd_card D)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at hdvdX
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd (hdvdX.trans (dvd_of_eq (by decide) : _ ∣ 6)) (by decide)
    · exact absurd (hdvdX.trans (dvd_of_eq (by decide) : _ ∣ 720)) (by decide)
  obtain ⟨t, r', hX, hadm, hmX, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ),
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g ∧
        (t = .PSL ∨ t = .PSp) := by
    rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
    · have hg2 : 2 ≤ g := by omega
      obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := k)
      have h4 : 4 ≤ 2 ^ g :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hadm : StatedLieAdmissible .PSL 2 2 g := ⟨Nat.prime_two, hg, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel X .PSL 2 2 g :=
        ⟨hadm, k, inferInstance, inferInstance, hk,
          ⟨(Φ.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm).trans
            e₂⟩⟩
      exact ⟨.PSL, 2, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩, Or.inl rfl⟩
    · have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
        · exact Or.inr (Or.inr ⟨by rw [hk, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r k) hk (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        Or.inr rfl⟩
  have hDtop := SeitzReduction.F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  have hDs : IsSimpleGroup D := eD.isSimpleGroup
  have htt := hdet.tag_eq_of_simple hD.1 hDs hC hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hmX)
  subst htt
  rcases ht₀ with h | h <;> rcases ht with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)

theorem EvenTagDet.false_of_spFixedOrNoPComponent (hdet : EvenTagDet C t₀)
    (ht₀ : t₀ = .PSU ∨ t₀ = .twistedB2)
    (h64 : ∀ (X : Type) [Group X], C X → 2 ^ 6 ∣ Nat.card X) {X : Type} [Group X] [Finite X]
    {g : ℕ} (h : SeitzReduction.LinearPilot.SpFixedOrNoPComponent X g) {D : Subgroup X}
    (hD : IsComponent D) (hC : C (D ⧸ center D)) : False := by
  rcases h with ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exact hdet.false_of_isComponent_statedSp ht₀ h64 hk hr Φ hD hC
  · exact h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)

theorem EvenTagDet.false_of_spFixedRankOrNoPComponent (hdet : EvenTagDet C t₀)
    (ht₀ : t₀ = .PSU ∨ t₀ = .twistedB2)
    (h64 : ∀ (X : Type) [Group X], C X → 2 ^ 6 ∣ Nat.card X) {X : Type} [Group X] [Finite X]
    {g : ℕ} {Q : ℕ → Prop} (h : SeitzReduction.RankOne.SpFixedRankOrNoPComponent X g Q)
    {D : Subgroup X} (hD : IsComponent D) (hC : C (D ⧸ center D)) : False := by
  rcases h with ⟨k, _, _, r, hk, hr, -, ⟨Φ⟩⟩ | h
  · exact hdet.false_of_isComponent_statedSp ht₀ h64 hk hr Φ hD hC
  · exact h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)

theorem EvenTagDet.false_of_omegaOuterFixed (hdet : EvenTagDet C t₀)
    (ht₀ : t₀ = .PSU ∨ t₀ = .twistedB2)
    (h64 : ∀ (X : Type) [Group X], C X → 2 ^ 6 ∣ Nat.card X) {X : Type} [Group X] [Finite X]
    {g : ℕ} (h : SeitzReduction.LinearPilot.OmegaOuterFixed X g) {D : Subgroup X}
    (hD : IsComponent D) (hC : C (D ⧸ center D)) : False := by
  rcases h with h | h
  · exact hdet.false_of_spFixedOrNoPComponent ht₀ h64 h hD hC
  · obtain ⟨t, n, f', ht, hadm, hmD⟩ :=
      h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)
    have htt := hdet.tag_eq_of_simple hD.1
      (SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_POmega ht hmD) hC hadm hmD
    subst htt
    rcases ht₀ with h | h <;> rcases ht with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)

theorem EvenTagDet.evenOuterFamilyOf_PSU (hdet : EvenTagDet C t₀)
    (ht₀ : t₀ = .PSU ∨ t₀ = .twistedB2)
    (h64 : ∀ (X : Type) [Group X], C X → 2 ^ 6 ∣ Nat.card X) : EvenOuterFamilyOf C R .PSU := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout D hD hC
  exact (hdet.false_of_spFixedOrNoPComponent ht₀ h64
    (SeitzReduction.LinearPilot.psu_outer_fixed_exact hadm hmS σ hσ hout) hD hC).elim

theorem EvenTagDet.evenOuterFamilyOf_POmega (hdet : EvenTagDet C t₀)
    (ht₀ : t₀ = .PSU ∨ t₀ = .twistedB2)
    (h64 : ∀ (X : Type) [Group X], C X → 2 ^ 6 ∣ Nat.card X) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) : EvenOuterFamilyOf C R t := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout D hD hC
  exact (hdet.false_of_omegaOuterFixed ht₀ h64
    (SeitzReduction.LinearPilot.omega_family_fixed_exact ht hadm hmS σ hσ hout) hD hC).elim

theorem two_pow_six_dvd_card_of_lieModel_PSU3 {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSU 3 2 f) : 2 ^ 6 ∣ Nat.card X := by
  have hf := two_le_of_lieModel_PSU3 h
  rw [card_eq_ordTwistedA_of_lieModel_PSU3 h]
  obtain ⟨hdvd, -, -⟩ :=
    SeitzReduction.UnitaryPilot.ordTwistedA_two_pow_bounds (n := 2) le_rfl (by omega : 1 ≤ f)
  exact (Nat.pow_dvd_pow 2 (by norm_num; omega)).trans hdvd

section Unitary

theorem evenTagDet_U3 (f : ℕ) : EvenTagDet (fun X _ => LieModel X .PSU 3 2 f) .PSU :=
  fun X _ t n g hX hadm h => (su3EvenTypeDet X f t n g hX hadm h).1

theorem evenOuterFamilyOf_PSL_U3 (f : ℕ) :
    EvenOuterFamilyOf (fun X _ => LieModel X .PSU 3 2 f) (fun S _ => LieModel S .PSL 3 2 (2 * f))
      .PSL := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout D hD hDm
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases SeitzReduction.UnitaryPilot.psl_outer_fixed_even hadm hmS σ hσ hout with
    h | ⟨he, h⟩ | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · obtain ⟨hadm', hmD, -⟩ := h D hDp
    exact absurd ((evenTagDet_U3 f).tag_eq_of_simple hD.1
      (SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) hDm hadm' hmD) (by decide)
  · obtain ⟨hadm', hmD⟩ := h D hDp
    obtain ⟨-, hnm, hef⟩ := SeitzReduction.UnitaryPilot.sumTypeDet_of_simple su3EvenTypeDet hD.1
      (SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSU hmD) hDm hadm' hmD
    subst hnm
    rw [← hef, he]
    exact hmS
  · exact ((evenTagDet_U3 f).false_of_isComponent_statedSp (Or.inl rfl)
      (fun _ _ h => two_pow_six_dvd_card_of_lieModel_PSU3 h) hk hr Φ hD hDm).elim
  · exact (h D hDp).elim

theorem evenOuterFamilyOf_PSp_U3 (f : ℕ) {R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf (fun X _ => LieModel X .PSU 3 2 f) R .PSp := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout D hD hDm
  rcases SeitzReduction.LinearPilot.psp_outer_fixed_exact hadm hmS σ hσ hout with
    h | ⟨hS, hadmB, hLie⟩
  · exact ((evenTagDet_U3 f).false_of_spFixedOrNoPComponent (Or.inl rfl)
      (fun _ _ h => two_pow_six_dvd_card_of_lieModel_PSU3 h) h hD hDm).elim
  · have hDtop := SeitzReduction.F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
    let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
    exact absurd ((evenTagDet_U3 f).tag_eq_of_simple hD.1 eD.isSimpleGroup hDm hadmB
      (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLie)) (by decide)

theorem no_su3_component_of_excInput {τ : StatedLieTag}
    (h : SeitzReduction.F4Pilot.EvenOuterFamilyExcInput τ) {S : Type} [Group S] [Finite S]
    {n e : ℕ} (hadm : StatedLieAdmissible τ n 2 e) (hmS : LieModel S τ n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU 3 2 f) : False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S n e hadm hmS σ hσ hout D hP
  have hZ : Open.fusionZStar D = center D :=
    ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hD.1
      (ComponentClassification.CatLeaf.pPrimeCore_ne_top_of_isPComponent hP)
  let E : D ⧸ Open.fusionZStar D ≃* D ⧸ center D := QuotientGroup.quotientMulEquivOfEq hZ
  rcases hX with ⟨τ', e', hτ', hadm', hm'⟩ | hU
  · obtain ⟨rfl, -, -⟩ := su3EvenTypeDet (D ⧸ center D) f τ' 0 e' hDm hadm'
      (LieType.CurtisTits.lieModel_of_mulEquiv E hm')
    exact hτ' (by decide)
  · have h1 := GH74.card_of_lieModel_PSU (by norm_num) (by norm_num)
      (LieType.CurtisTits.lieModel_of_mulEquiv E hU)
    rw [show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide] at h1
    have h64 := two_pow_six_dvd_card_of_lieModel_PSU3 hDm
    rw [h1] at h64
    exact absurd h64 (by decide)

theorem evenOuterFamilyOf_of_excInput_U3 {τ : StatedLieTag}
    (h : SeitzReduction.F4Pilot.EvenOuterFamilyExcInput τ) (f : ℕ)
    {R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf (fun X _ => LieModel X .PSU 3 2 f) R τ :=
  fun _ _ _ _ _ _ _ hadm hmS _ hσ hout _ hD hDm =>
    (no_su3_component_of_excInput h hadm hmS hσ hout hD hDm).elim

end Unitary

theorem two_pow_six_dvd_card_of_lieModel_twistedB2 {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .twistedB2 0 2 f) : 2 ^ 6 ∣ Nat.card X := by
  have hf := three_le_of_lieModel_twistedB2 h
  calc 2 ^ 6 ∣ 2 ^ (2 * f) := Nat.pow_dvd_pow 2 (by omega)
    _ = 2 ^ (Nat.card X).factorization 2 := by rw [factorization_two_card_of_lieModel_twistedB2 h]
    _ ∣ Nat.card X := Nat.ordProj_dvd _ _

section Symplectic

open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial SymplecticFlag
  SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem psp_outer_fixed_rank_two {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel J .PSp n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SeitzReduction.RankOne.SpFixedRankOrNoPComponent (fixedSubgroup α) (e / 2) (fun r => r = n) ∨
      (n = 2 ∧ IsSimpleGroup (fixedSubgroup α) ∧ StatedLieAdmissible .twistedB2 0 2 e ∧
        LieModel (fixedSubgroup α) .twistedB2 0 2 e) := by
  have hn : 2 ≤ n := hadm.2.2.1
  by_cases hn3 : 3 ≤ n
  · left
    obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel hadm hm
    have hf : 1 ≤ e := hadm.2.1
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    have : NeZero n := ⟨by omega⟩
    have hβ : orderOf (MulAut.congr eJ α) = 2 :=
      (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
    have hβ2 : MulAut.congr eJ α * MulAut.congr eJ α = 1 := by
      rw [← sq, ← hβ, pow_orderOf_eq_one]
    have hβo : MulAut.congr eJ α ∉ inner (StatedProj (StatedSp n K)) := by
      rw [FixedFourGroup.congr_mem_inner_iff]
      exact hαo
    have hmem : MulAut.congr eJ α ∈ spSemilinearAutGroup n K := by
      rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
      exact mem_top _
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    obtain ⟨k, _, _, hk, -, ⟨Φ⟩⟩ := SeitzReduction.F4Pilot.psp_field_fixed hn hf hK hβ2 g σ hgσ hσ
    exact Or.inl ⟨k, inferInstance, inferInstance, n, hk, by omega, rfl,
      ⟨(fixedSubgroupCongrEquiv eJ α).trans Φ⟩⟩
  · obtain rfl : n = 2 := by omega
    rcases SeitzReduction.RankOne.psp_outer_fixed_rank hadm hm α hα hαo with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩

end Symplectic

@[expose] def ExcEvenTypeNoSz (X : Type) [Group X] : Prop :=
  (∃ (τ : StatedLieTag) (e : ℕ), τ ∉ classicalTags ∧ τ ≠ .twistedB2 ∧
      StatedLieAdmissible τ 0 2 e ∧ LieModel X τ 0 2 e) ∨
    LieModel X .PSU 3 3 1

@[expose] def EvenOuterFamilyExcNoSzInput (τ : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f → LieModel K τ n 2 f →
    ∀ α : MulAut K, orderOf α = 2 → α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P →
      ExcEvenTypeNoSz (P ⧸ Open.fusionZStar P)

section Exceptional

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.F4Pilot
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem evenOuterFamilyExcNoSzInput_G2 :
    EvenOuterFamilyExcNoSzInput .G2 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hq : 3 ≤ 2 ^ f := hadm.2.2.2
  have hf2 : 2 ≤ f := by
    by_contra h
    interval_cases f <;> norm_num at hq
  have hu : UntwistedChevalleyModel K .G2 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hu
  have : Finite (ModGL .G2 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .G2 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ := even_G2_outer_fixed hf2 hF β hβ2 hβo
  have : Finite (ModGL .G2 k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  rcases Nat.lt_or_ge e' 2 with he1 | he2
  · obtain rfl : e' = 1 := by omega
    have hk2 : Nat.card k = 2 := by simpa using hk
    have hL := Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk2
    have hs : IsSimpleGroup ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ := by
      rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact (ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 h).2
      all_goals exact absurd h (by norm_num)
    have hD : IsSimpleGroup (commutator ↥(adjointGroup .G2 k)) :=
      (commutatorSubtypeEquiv (adjointGroup .G2 k)).isSimpleGroup
    have hPeq := eq_commutator_of_isPComponent hD
      (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ hP)
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
      (((P.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans
        (MulEquiv.subgroupCongr hPeq)).trans (commutatorSubtypeEquiv (adjointGroup .G2 k)))
    exact Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv E.symm hL)
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Ψ hP
    exact Or.inl ⟨.G2, e', by decide, by decide, lieModel_G2_of_mulEquiv he2 hk E⟩

theorem evenOuterFamilyExcNoSzInput_F4 :
    EvenOuterFamilyExcNoSzInput .F4 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .F4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hu
  have : Finite (ModGL .F4 F) := finite_modGL
  have : Finite (ModGL ReeTag.F4.tag F) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag F) := Subtype.finite
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .F4 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : CharP F ReeTag.F4.prime := ‹CharP F 2›
  rcases even_F4_outer_fixed hf hF β hβ2 hβo with ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ | ⟨m, hfm, ⟨Φ⟩⟩
  · have : Finite (ModGL .F4 k) := finite_modGL
    have := (ExcSelector.adjointGroup_F4_even he' hk).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
      ((fixedSubgroupCongrEquiv e α).trans Φ) hP
    exact Or.inl ⟨.F4, e', by decide, by decide, lieModel_F4_of_mulEquiv he' hk E⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have hF2 : Nat.card F = 2 := by rw [hF, hfm]; rfl
      exact Or.inl ⟨.Tits, 1, by decide, by decide, lieModel_tits_of_isPComponent hF2
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP⟩
    · have hF' : Nat.card F = 2 ^ (2 * m + 1) := hfm ▸ hF
      have := (ExcSelector.reeFixed_F4_simple_not_smallType hm1 hF').1
      obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      exact Or.inl ⟨.twistedF4, 2 * m + 1, by decide, by decide,
        lieModel_twistedF4_of_mulEquiv hm1 hF' E⟩

theorem evenOuterFamilyExcNoSzInput_E6 :
    EvenOuterFamilyExcNoSzInput .E6 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hu
  have : Finite (ModGL .E6 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E6 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  rcases EvenExc.even_E6_outer_lieModel_exact hf hF β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
    with h | ⟨e', -, he', h | h⟩
  · exact Or.inl ⟨.F4, f, by decide, by decide, ⟨Nat.prime_two, hf, rfl⟩, h⟩
  · exact Or.inl ⟨.E6, e', by decide, by decide, ⟨Nat.prime_two, he', rfl⟩, h⟩
  · exact Or.inl ⟨.twistedE6, e', by decide, by decide, ⟨Nat.prime_two, he', rfl⟩, h⟩

theorem evenOuterFamilyExcNoSzInput_twistedE6 :
    EvenOuterFamilyExcNoSzInput .twistedE6 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact Or.inl ⟨.F4, f, by decide, by decide,
    even_twistedE6_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP⟩

theorem evenOuterFamilyExcNoSzInput_E7_E8
    {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8) : EvenOuterFamilyExcNoSzInput t := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨τ, hτ, htτ, hu⟩ : ∃ τ : Tag, (τ = .E7 ∨ τ = .E8) ∧
      (t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) ∧ UntwistedChevalleyModel K τ (2 ^ f) := by
    rcases ht with rfl | rfl
    · exact ⟨.E7, Or.inl rfl, Or.inl ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
    · exact ⟨.E8, Or.inr rfl, Or.inr ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hu
  have : Finite (ModGL τ F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup τ F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', he', k, _, _, hk, hs, ⟨Φ⟩⟩ := even_E7_E8_outer_fixed hτ hf hF β hβ2 hβo
  have : Finite (ModGL τ k) := finite_modGL
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
    ((fixedSubgroupCongrEquiv e α).trans Φ) hP
  exact Or.inl ⟨t, e', by rcases ht with rfl | rfl <;> decide,
    by rcases ht with rfl | rfl <;> decide,
    lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ he' hk E⟩

theorem evenOuterFamilyExcNoSzInput_trialityD4 :
    EvenOuterFamilyExcNoSzInput .trialityD4 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .D4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.D4.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', hadm', hL⟩ :=
    even_triality_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact Or.inl ⟨.trialityD4, e', by decide, by decide, hadm', hL⟩

end Exceptional

section Suzuki

theorem evenTagDet_Sz (f : ℕ) : EvenTagDet (fun X _ => LieModel X .twistedB2 0 2 f) .twistedB2 :=
  fun X _ t n g hX hadm h => (szEvenTypeDet X f t n g hX hadm h).1

theorem szTypeDet_of_simple {D : Type} [Group D] (hq : IsQuasisimple D) (hs : IsSimpleGroup D)
    {f : ℕ} (hDm : LieModel (D ⧸ center D) .twistedB2 0 2 f) {t : StatedLieTag} {n f' : ℕ}
    (hadm : StatedLieAdmissible t n 2 f') (hD : LieModel D t n 2 f') :
    t = .twistedB2 ∧ n = 0 ∧ f' = f :=
  szEvenTypeDet (D ⧸ center D) f t n f' hDm hadm
    (SeitzReduction.LinearPilot.lieModel_quotient_center_of_center_eq_bot
      (SeitzReduction.F4Pilot.center_eq_bot_of_isQuasisimple hq hs) hD)

theorem evenOuterFamilyOf_PSL_Sz (f : ℕ) {R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf (fun X _ => LieModel X .twistedB2 0 2 f) R .PSL := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout D hD hDm
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases SeitzReduction.UnitaryPilot.psl_outer_fixed_even hadm hmS σ hσ hout with
    h | ⟨-, h⟩ | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · obtain ⟨hadm', hmD, -⟩ := h D hDp
    exact absurd ((evenTagDet_Sz f).tag_eq_of_simple hD.1
      (SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) hDm hadm' hmD) (by decide)
  · obtain ⟨hadm', hmD⟩ := h D hDp
    exact absurd ((evenTagDet_Sz f).tag_eq_of_simple hD.1
      (SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSU hmD) hDm hadm' hmD) (by decide)
  · exact ((evenTagDet_Sz f).false_of_isComponent_statedSp (Or.inr rfl)
      (fun _ _ h => two_pow_six_dvd_card_of_lieModel_twistedB2 h) hk hr Φ hD hDm).elim
  · exact (h D hDp).elim

theorem evenOuterFamilyOf_PSp_Sz (f : ℕ) :
    EvenOuterFamilyOf (fun X _ => LieModel X .twistedB2 0 2 f) (fun S _ => LieModel S .PSp 2 2 f)
      .PSp := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout D hD hDm
  rcases psp_outer_fixed_rank_two hadm hmS σ hσ hout with h | ⟨rfl, hS, hadmB, hLie⟩
  · exact ((evenTagDet_Sz f).false_of_spFixedRankOrNoPComponent (Or.inr rfl)
      (fun _ _ h => two_pow_six_dvd_card_of_lieModel_twistedB2 h) h hD hDm).elim
  · have hDtop := SeitzReduction.F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
    let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
    obtain ⟨-, -, hef⟩ := szTypeDet_of_simple hD.1 eD.isSimpleGroup hDm hadmB
      (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLie)
    subst hef
    exact hmS

theorem no_sz_component_of_excNoSzInput {τ : StatedLieTag} (h : EvenOuterFamilyExcNoSzInput τ)
    {S : Type} [Group S] [Finite S] {n e : ℕ} (hadm : StatedLieAdmissible τ n 2 e)
    (hmS : LieModel S τ n 2 e) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {f : ℕ} {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .twistedB2 0 2 f) : False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S n e hadm hmS σ hσ hout D hP
  have hZ : Open.fusionZStar D = center D :=
    ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hD.1
      (ComponentClassification.CatLeaf.pPrimeCore_ne_top_of_isPComponent hP)
  let E : D ⧸ Open.fusionZStar D ≃* D ⧸ center D := QuotientGroup.quotientMulEquivOfEq hZ
  apply not_three_dvd_card_of_lieModel_twistedB2 hDm
  rw [← Nat.card_congr E.toEquiv]
  rcases hX with ⟨τ', e', -, hτ', hadm', hm'⟩ | hU
  · exact three_dvd_card_of_lieModel hadm' hm' hτ'
  · rw [GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) hU,
      show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide]
    norm_num

theorem evenOuterFamilyOf_of_excNoSzInput_Sz {τ : StatedLieTag}
    (h : EvenOuterFamilyExcNoSzInput τ) (f : ℕ) {R : (X : Type) → [Group X] → Prop} :
    EvenOuterFamilyOf (fun X _ => LieModel X .twistedB2 0 2 f) R τ :=
  fun _ _ _ _ _ _ _ hadm hmS _ hσ hout _ hD hDm =>
    (no_sz_component_of_excNoSzInput h hadm hmS hσ hout hD hDm).elim

end Suzuki

end CatEvenBender

open CatEvenBender

section UnitaryList

theorem catSU3EvenOuterList (f : ℕ) :
    EvenOuterListOf (fun X _ => LieModel X .PSU 3 2 f)
      (fun S _ => LieModel S .PSL 3 2 (2 * f)) := by
  have h64 : ∀ (X : Type) [Group X], LieModel X .PSU 3 2 f → 2 ^ 6 ∣ Nat.card X :=
    fun _ _ h => two_pow_six_dvd_card_of_lieModel_PSU3 h
  have hdet := evenTagDet_U3 f
  exact evenOuterListOf_of_open_families (evenOuterFamilyOf_PSL_U3 f)
    (hdet.evenOuterFamilyOf_PSU (Or.inl rfl) h64) (evenOuterFamilyOf_PSp_U3 f)
    (hdet.evenOuterFamilyOf_POmega (Or.inl rfl) h64 (Or.inl rfl))
    (hdet.evenOuterFamilyOf_POmega (Or.inl rfl) h64 (Or.inr rfl))
    (evenOuterFamilyOf_of_excInput_U3 SeitzReduction.F4Pilot.evenOuterFamilyExcInput_G2 f)
    (evenOuterFamilyOf_of_excInput_U3 SeitzReduction.F4Pilot.evenOuterFamilyExcInput_F4 f)
    (evenOuterFamilyOf_of_excInput_U3 SeitzReduction.F4Pilot.evenOuterFamilyExcInput_E6 f)
    (evenOuterFamilyOf_of_excInput_U3
      (SeitzReduction.F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inl rfl)) f)
    (evenOuterFamilyOf_of_excInput_U3
      (SeitzReduction.F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inr rfl)) f)
    (evenOuterFamilyOf_of_excInput_U3 SeitzReduction.F4Pilot.evenOuterFamilyExcInput_twistedE6 f)
    (evenOuterFamilyOf_of_excInput_U3 SeitzReduction.F4Pilot.evenOuterFamilyExcInput_trialityD4 f)

end UnitaryList

section SuzukiList

theorem catSzEvenOuterList (f : ℕ) :
    EvenOuterListOf (fun X _ => LieModel X .twistedB2 0 2 f)
      (fun S _ => LieModel S .PSp 2 2 f) := by
  have h64 : ∀ (X : Type) [Group X], LieModel X .twistedB2 0 2 f → 2 ^ 6 ∣ Nat.card X :=
    fun _ _ h => two_pow_six_dvd_card_of_lieModel_twistedB2 h
  have hdet := evenTagDet_Sz f
  exact evenOuterListOf_of_open_families (evenOuterFamilyOf_PSL_Sz f)
    (hdet.evenOuterFamilyOf_PSU (Or.inr rfl) h64) (evenOuterFamilyOf_PSp_Sz f)
    (hdet.evenOuterFamilyOf_POmega (Or.inr rfl) h64 (Or.inl rfl))
    (hdet.evenOuterFamilyOf_POmega (Or.inr rfl) h64 (Or.inr rfl))
    (evenOuterFamilyOf_of_excNoSzInput_Sz evenOuterFamilyExcNoSzInput_G2 f)
    (evenOuterFamilyOf_of_excNoSzInput_Sz evenOuterFamilyExcNoSzInput_F4 f)
    (evenOuterFamilyOf_of_excNoSzInput_Sz evenOuterFamilyExcNoSzInput_E6 f)
    (evenOuterFamilyOf_of_excNoSzInput_Sz (evenOuterFamilyExcNoSzInput_E7_E8 (Or.inl rfl)) f)
    (evenOuterFamilyOf_of_excNoSzInput_Sz (evenOuterFamilyExcNoSzInput_E7_E8 (Or.inr rfl)) f)
    (evenOuterFamilyOf_of_excNoSzInput_Sz evenOuterFamilyExcNoSzInput_twistedE6 f)
    (evenOuterFamilyOf_of_excNoSzInput_Sz evenOuterFamilyExcNoSzInput_trialityD4 f)

end SuzukiList

end CFSG.LocalAnalysis.EvenBN.GMSK
