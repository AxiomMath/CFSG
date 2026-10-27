module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep74
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseCSp
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDFusion

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

@[expose] def SymplecticCase1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A) (R T : Subgroup G)
    (g : G), D.family = .symplectic → RankTwoClassicalEvenType (rankTwoQuot A) → 4 ≤ D.q →
    MinChoice D R T g → ∀ t ∈ T, t ≠ 1 → ∀ p ∈ A, t⁻¹ * p ∈ R →
      D.HasMeasure p (choiceMeasure D R T) → ¬ D.IsPrimary p → Case1 D p → False

@[expose] def SymplecticCase1Type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ (p : G) (ℓ : ℕ), ((1 < ℓ ∧ D.SuzukiType p .b ℓ) ∨ D.SuzukiType p .c ℓ) →
        ¬ Case1 D p

@[expose] def SymplecticCaseCTypeA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A) (R T : Subgroup G)
    (g : G), D.family = .symplectic → RankTwoClassicalEvenType (rankTwoQuot A) → 4 ≤ D.q →
    MinChoice D R T g → T ⊓ A = ⊥ → ∀ t ∈ T, t ≠ 1 → ∀ p ∈ A, t⁻¹ * p ∈ R →
      D.HasMeasure p (choiceMeasure D R T) → ∀ ℓ : ℕ, D.SuzukiType p .a ℓ → Case1 D p → False

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ClassicalModel.exists_suzukiType_symplectic {A : Subgroup G} (D : ClassicalModel A)
    (hfam : D.family = .symplectic) (hZ : Odd (Nat.card (center ↥A))) {x : G} (hx : x ∈ A)
    (hx2 : orderOf x = 2) : ∃ (L : Letter) (ℓ : ℕ), D.SuzukiType x L ℓ := by
  have hxZ := not_mem_center_of_orderOf_eq_two hZ hx hx2
  have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  cases D with
  | linear => simp [ClassicalModel.family] at hfam
  | unitary => simp [ClassicalModel.family] at hfam
  | orthPlus => simp [ClassicalModel.family] at hfam
  | orthMinus => simp [ClassicalModel.family] at hfam
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hx hx2' hxZ
    obtain ⟨L, hL⟩ := exists_letterHolds (commRank M) fun v =>
      sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).mulVec v)
    exact ⟨L, _, hx2, M, hM, hM2, rfl, hL⟩

theorem symplecticCase1_of (I : Inputs74) (hAP : SymplecticTypeAPerfect)
    (hT1 : SymplecticCase1Type) (hCC : SymplecticCaseCTypeA) : SymplecticCase1 := by
  intro G _ _ A D R T g hfam hTy hq hm t ht ht1 p hp hρ hpn hnp h1
  have hc := hm.sec3
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ : Odd (Nat.card (center ↥A)) :=
    (I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).1
  have hp2 := hc.orderOf_aPart I.h32 ht ht1 hρ
  obtain ⟨L, ℓ, hL⟩ := D.exists_suzukiType_symplectic hfam hZ hp hp2
  cases L with
  | a =>
    rcases hc.inf_eq_bot_or_eq_of_typeA I hTy D hfam hq ht ht1 hp hρ hL with hTA | hTA
    · exact hCC G A D R T g hfam hTy hq hm hTA t ht ht1 p hp hρ hpn ℓ hL h1
    · have htA : t ∈ A := (hTA.le ht |> mem_inf.mp).2
      have hpt : p = t := hc.aPart_unique hZ hp hρ htA (by rw [inv_mul_cancel]; exact one_mem _)
      subst hpt
      exact hc.false_of_mem_perfectCore I.h4 I.h32 I.h34 hOut hZ ht ht1
        (hAP G A D hfam hc.hyp.standard.1 hZ hq p ℓ hL)
  | b =>
    have hpos := D.pos_of_hasRank (D.hasRank_of_suzukiType hL)
    by_cases hℓ : ℓ = 1
    · subst hℓ
      exact hnp (D.isPrimary_of_suzukiType_b_one hfam hL)
    · exact hT1 G A D hfam hc.hyp.standard.1 hZ hq p ℓ (Or.inl ⟨by omega, hL⟩) h1
  | c => exact hT1 G A D hfam hc.hyp.standard.1 hZ hq p ℓ (Or.inr hL) h1

theorem symplecticCaseCTypeA_of (I : Inputs74) (hSA : SymplecticSplitA)
    (hPA : SymplecticPairA2) : SymplecticCaseCTypeA := by
  intro G _ _ A D R T g hfam hTy hq hm hTA t ht ht1 p hp hρ hpn ℓ hpa h1
  exact hm.false_of_caseC_typeA I hTy D hfam hq hSA hPA hTA ht ht1 hp hρ hpn hpa h1

theorem Sec3.case123_symplectic {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g) (I : Inputs74)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
    (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) :
    ((∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p) ∧ Nat.card T ≤ D.q ∧
      (Case1 D p ∨ Case23 D p)) ∨ CaseII D T := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  obtain ⟨-, -, h⟩ := I.h222 G A T D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)
  rcases h t ht ht1 p (hc.isAPart I.h32 ht hp hρ) with ⟨hle, hT, hI⟩ | hII
  · refine Or.inl ⟨fun t' ht' p' hp' hρ' => hle t' ht' p' (hc.isAPart I.h32 ht' hp' hρ'), hT, ?_⟩
    simpa only [CaseI, hfam] using hI
  · exact hII.elim

theorem step74_of_symplectic (I : Inputs74) (h117 : ClassicalPrimaryPerfect)
    (h33 : Lemma33Three) (h73 : Step73) (hAP : SymplecticTypeAPerfect) (hC1 : SymplecticCase1)
    {A : Subgroup G} (D : ClassicalModel A) (hfam : D.family = .symplectic) (hA : Hyp31 A)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) :
    ∃ (R T : Subgroup G) (g : G), Choice74 D R T g := by
  have hq := h73 G A D hA hTy
  have hOut := I.hOut ↥A hA.standard.1.1 hTy
  obtain ⟨g₀, hg₀, R, T₀, hR, hT₀, -, -, hTR, -, -⟩ := section3Config_of I.h32 h33 I.h4 I.h34 G A hA
  have hc₀ : Sec3 A R T₀ g₀ := ⟨hA, hR, hg₀, hT₀, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  obtain ⟨T, g, hm⟩ := exists_minChoice D hc₀
  have hc := hm.sec3
  have hZ : Odd (Nat.card (center ↥A)) :=
    (I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).1
  obtain ⟨t, ht, ht1, p, hp, hρ, hpn⟩ := hc.exists_choiceMeasure I.h32 I.h4 I.h34 D hZ
  have hprim : D.IsPrimary p := by
    by_contra hnp
    rcases hc.case123_symplectic I hTy D hfam hq ht ht1 hp hρ with ⟨-, -, h1 | h23⟩ | hII
    · exact hC1 G A D R T g hfam hTy hq hm t ht ht1 p hp hρ hpn hnp h1
    · by_cases hTA : T ≤ A
      · exact hc.false_of_case23_of_le I hTy D hfam hq h117 hAP hTA ht ht1 hp hρ h23
      · exact hm.false_of_case23 I hTy D hfam hq hTA ht ht1 hp hρ hpn h23
    · have := hII.2.2
      omega
  obtain ⟨-, hfus, -⟩ := I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)
  have hall : ∀ t' ∈ T, t' ≠ 1 → ∀ p' ∈ A, t'⁻¹ * p' ∈ R → D.IsPrimary p' := by
    intro t' ht' ht'1 p' hp' hρ'
    obtain ⟨b, hb, hbp⟩ := hfus t ht ht1 t' ht' ht'1 p p' (hc.isAPart I.h32 ht hp hρ)
      (hc.isAPart I.h32 ht' hp' hρ')
    rw [← hbp]
    exact D.isPrimary_conj hprim hb
  have hTA := hc.inf_eq_bot_of_primary I.h4 I.h32 I.h34 h117 D hq hOut hZ hall
  refine ⟨R, T, g, hc.sylowR, hc.not_mem, hc.sylowT, hc.le_centralizer, hTA, hall, ?_, hZ, hq⟩
  intro x hx
  apply hc.T_ne_bot
  rw [← hTA]
  exact (inf_eq_left.mpr (hm.le_of_le _ x (hc.sec3_of_le I.h32 hZ hx) hx)).symm

theorem step74_of (I : Inputs74) (hS : ClassicalSplit) (h117 : ClassicalPrimaryPerfect)
    (h33 : Lemma33Three) (h73 : Step73) (hAP : SymplecticTypeAPerfect)
    (hT1 : SymplecticCase1Type) (hSA : SymplecticSplitA) (hPA : SymplecticPairA2) : Step74 := by
  intro G _ _ A D hA hTy
  by_cases hfam : D.family = .symplectic
  · exact step74_of_symplectic I h117 h33 h73 hAP
      (symplecticCase1_of I hAP hT1 (symplecticCaseCTypeA_of I hSA hPA)) D hfam hA hTy
  · exact step74_of_ne_symplectic I hS h117 h33 h73 D hfam hA hTy

end CFSG.ComponentClassification.RankTwoClassical
