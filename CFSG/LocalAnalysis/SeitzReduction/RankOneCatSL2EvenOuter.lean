module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuterOmega
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarCat
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (EvenOuterFamilyExcInput)

@[expose] def CatSL2EvenOuterFamily (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ m e : ℕ, StatedLieAdmissible τ m 2 e → LieModel S τ m 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ D : Subgroup (fixedSubgroup σ), IsComponent D → LieModel (D ⧸ center D) .PSL 2 2 n →
      LieModel S .PSL 2 2 (2 * n) ∨ LieModel S .PSU 3 2 n ∨ LieModel S .PSL 3 2 n

theorem catSL2EvenOuterList_of_families {n : ℕ} (h : ∀ τ, CatSL2EvenOuterFamily τ n) :
    CatSL2EvenOuterList n := by
  rintro S _ _ hS hna heven σ hout ⟨hσ, D, hD, hDm, -⟩
  obtain ⟨τ, m, e, hadm, hmS⟩ := heven
  exact h τ S hS hna m e hadm hmS σ hσ hout D hD hDm

theorem catSL2EvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ m e : ℕ, ¬ StatedLieAdmissible τ m 2 e) (n : ℕ) : CatSL2EvenOuterFamily τ n :=
  fun _ _ _ _ _ m e hadm => absurd hadm (hτ m e)

theorem catSL2EvenOuterFamily_POmegaOdd (n : ℕ) : CatSL2EvenOuterFamily .POmegaOdd n :=
  catSL2EvenOuterFamily_of_not_admissible (τ := .POmegaOdd) (fun _ _ hadm => hadm.2.2.2 rfl) n

theorem catSL2EvenOuterFamily_twistedG2 (n : ℕ) : CatSL2EvenOuterFamily .twistedG2 n :=
  catSL2EvenOuterFamily_of_not_admissible (τ := .twistedG2)
    (fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)) n

theorem catSL2EvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (m e : ℕ), StatedLieAdmissible τ m 2 e → LieModel K τ m 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) (n : ℕ) :
    CatSL2EvenOuterFamily τ n := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout
  exact absurd (hτ S m e hadm hmS σ (hσ ▸ pow_orderOf_eq_one σ)) hout

theorem catSL2EvenOuterFamily_PSL (hdet : SL2EvenTypeDet) (n : ℕ) :
    CatSL2EvenOuterFamily .PSL n := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout D hD hDm
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases psl_outer_fixed_rank hadm hmS σ hσ hout with h | h |
      ⟨k, _, _, r, hk, hr, ⟨hm3, hmr⟩, ⟨Φ⟩⟩ | h
  · obtain ⟨hadm', hmD, he⟩ := h D hDp
    obtain ⟨-, hm2, hen⟩ := sl2TypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) hDm hadm' hmD
    subst hm2
    left
    rw [← hen, he]
    exact hmS
  · obtain ⟨hadm', hmD⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := sl2TypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSU hmD) hDm hadm' hmD
    exact absurd htt (by decide)
  · obtain ⟨rfl, rfl⟩ := rank_eq_one_of_isComponent_statedSp hdet hk hr Φ hD hDm
    obtain rfl : m = 3 := by omega
    exact Or.inr (Or.inr hmS)
  · exact (h D hDp).elim

theorem catSL2EvenOuterFamily_PSU (hdet : SL2EvenTypeDet) (n : ℕ) :
    CatSL2EvenOuterFamily .PSU n := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout D hD hDm
  rcases psu_outer_fixed_rank hadm hmS σ hσ hout with ⟨k, _, _, r, hk, hr, hmr, ⟨Φ⟩⟩ | h
  · obtain ⟨rfl, rfl⟩ := rank_eq_one_of_isComponent_statedSp hdet hk hr Φ hD hDm
    have hm3 : 3 ≤ m := hadm.2.2.1
    obtain rfl : m = 3 := by omega
    exact Or.inr (Or.inl hmS)
  · exact (h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)).elim

theorem catSL2EvenOuterFamily_PSp (hdet : SL2EvenTypeDet)
    (n : ℕ) : CatSL2EvenOuterFamily .PSp n := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout D hD hDm
  rcases psp_outer_fixed_rank hadm hmS σ hσ hout with
      (⟨k, _, _, r, hk, hr, hrm, ⟨Φ⟩⟩ | h) | ⟨hS, hadmB, hLie⟩
  · obtain ⟨h1, -⟩ := rank_eq_one_of_isComponent_statedSp hdet hk hr Φ hD hDm
    have : 2 ≤ m := hadm.2.2.1
    omega
  · exact (h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)).elim
  · have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
    let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
    have hDs : IsSimpleGroup D := eD.isSimpleGroup
    obtain ⟨htt, -, -⟩ := sl2TypeDet_of_simple hdet hD.1 hDs hDm hadmB
      (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLie)
    exact absurd htt (by decide)

theorem catSL2EvenOuterFamily_POmega {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (hdet : SL2EvenTypeDet) (n : ℕ) : CatSL2EvenOuterFamily t n := by
  intro S _ _ _ _ m e hadm hmS σ hσ hout D hD hDm
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases omega_family_fixed_rank ht hadm hmS σ hσ hout with
      (⟨k, _, _, r, hk, hr, hrm, ⟨Φ⟩⟩ | h) | h
  · obtain ⟨h1, -⟩ := rank_eq_one_of_isComponent_statedSp hdet hk hr Φ hD hDm
    have : 4 ≤ m := by rcases ht with rfl | rfl <;> exact hadm.2.2
    omega
  · exact (h D hDp).elim
  · obtain ⟨t', m', f', ht', hadm', hmD⟩ := h D hDp
    obtain ⟨rfl, -, -⟩ := sl2TypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_POmega ht' hmD) hDm hadm' hmD
    rcases ht' with h | h <;> exact absurd h (by decide)

theorem ordA_one_ne_6048 {f : ℕ} (hf : 1 ≤ f) : Open.ordA 1 (2 ^ f) ≠ 6048 := by
  intro h
  rw [RankThree.PartOne.S12K.ordA_one_eq hf] at h
  have h5 : f = 5 := Timmesfeld.Orders.eq_of_two_pow_mul_odd
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by omega)) (by decide : Odd 189)
    (h.trans (by norm_num : (6048 : ℕ) = 2 ^ 5 * 189))
  subst h5
  revert h
  decide

theorem no_sl2_component_of_excInput (hdet : SL2EvenTypeDet) {τ : StatedLieTag}
    (h : EvenOuterFamilyExcInput τ) {S : Type} [Group S] [Finite S] {m e : ℕ}
    (hadm : StatedLieAdmissible τ m 2 e) (hmS : LieModel S τ m 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {n : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 2 2 n) : False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S m e hadm hmS σ hσ hout D hP
  have hZ : Open.fusionZStar D = center D :=
    ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hD.1
      (ComponentClassification.CatLeaf.pPrimeCore_ne_top_of_isPComponent hP)
  let E : D ⧸ Open.fusionZStar D ≃* D ⧸ center D := QuotientGroup.quotientMulEquivOfEq hZ
  rcases hX with ⟨τ', e', -, hadm', hm'⟩ | hU
  · obtain ⟨-, h02, -⟩ :=
      hdet (D ⧸ center D) n τ' 0 e' hDm hadm' (LieType.CurtisTits.lieModel_of_mulEquiv E hm')
    exact absurd h02 (by norm_num)
  · have hn : 1 ≤ n := (F4Pilot.statedLieAdmissible_of_lieModel hDm).2.1
    have h1 := GH74.card_of_lieModel_PSU (by norm_num) (by norm_num)
      (LieType.CurtisTits.lieModel_of_mulEquiv E hU)
    rw [card_of_lieModel_PSL_two_two hDm,
      show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide] at h1
    exact ordA_one_ne_6048 hn h1

theorem catSL2EvenOuterFamily_of_excInput (hdet : SL2EvenTypeDet) {τ : StatedLieTag}
    (h : EvenOuterFamilyExcInput τ) (n : ℕ) : CatSL2EvenOuterFamily τ n :=
  fun _ _ _ _ _ _ _ hadm hmS _ hσ hout _ hD hDm =>
    (no_sl2_component_of_excInput hdet h hadm hmS hσ hout hD hDm).elim

section SuzukiReeTits


theorem catSL2EvenOuterFamily_twistedB2 (n : ℕ) : CatSL2EvenOuterFamily .twistedB2 n := by
  refine catSL2EvenOuterFamily_of_involutions_inner (τ := .twistedB2)
    (fun K _ m e _ hmK => ?_) n
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem catSL2EvenOuterFamily_twistedF4 (n : ℕ) : CatSL2EvenOuterFamily .twistedF4 n := by
  refine catSL2EvenOuterFamily_of_involutions_inner (τ := .twistedF4)
    (fun K _ m e _ hmK => ?_) n
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSL2EvenOuterFamily_Tits (n : ℕ) : CatSL2EvenOuterFamily .Tits n := by
  refine catSL2EvenOuterFamily_of_involutions_inner (τ := .Tits)
    (fun K _ m e hadm hmK => ?_) n
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

end SuzukiReeTits

section List


theorem catSL2EvenOuterList (n : ℕ) : CatSL2EvenOuterList n := by
  have hdet := sl2EvenTypeDet
  apply catSL2EvenOuterList_of_families
  intro τ
  cases τ
  · exact catSL2EvenOuterFamily_PSL hdet n
  · exact catSL2EvenOuterFamily_PSU hdet n
  · exact catSL2EvenOuterFamily_PSp hdet n
  · exact catSL2EvenOuterFamily_POmegaOdd n
  · exact catSL2EvenOuterFamily_POmega (Or.inl rfl) hdet n
  · exact catSL2EvenOuterFamily_POmega (Or.inr rfl) hdet n
  · exact catSL2EvenOuterFamily_of_excInput hdet F4Pilot.evenOuterFamilyExcInput_G2 n
  · exact catSL2EvenOuterFamily_of_excInput hdet F4Pilot.evenOuterFamilyExcInput_F4 n
  · exact catSL2EvenOuterFamily_of_excInput hdet F4Pilot.evenOuterFamilyExcInput_E6 n
  · exact catSL2EvenOuterFamily_of_excInput hdet
      (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inl rfl)) n
  · exact catSL2EvenOuterFamily_of_excInput hdet
      (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inr rfl)) n
  · exact catSL2EvenOuterFamily_of_excInput hdet F4Pilot.evenOuterFamilyExcInput_twistedE6 n
  · exact catSL2EvenOuterFamily_of_excInput hdet F4Pilot.evenOuterFamilyExcInput_trialityD4 n
  · exact catSL2EvenOuterFamily_twistedB2 n
  · exact catSL2EvenOuterFamily_twistedG2 n
  · exact catSL2EvenOuterFamily_twistedF4 n
  · exact catSL2EvenOuterFamily_Tits n

end List

end CFSG.SeitzReduction.RankOne
