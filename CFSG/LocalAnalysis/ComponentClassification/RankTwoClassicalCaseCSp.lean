module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCoverSp
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplitSp

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem ClassicalModel.hasMeasure_of_suzukiType_c (D : ClassicalModel A) {x : G} {ℓ : ℕ}
    (h : D.SuzukiType x .c ℓ) (hfam : D.family = .symplectic) :
    D.HasMeasure x (3 * ℓ + 1) := by
  have hr := D.hasRank_of_suzukiType h
  obtain ⟨k, hk⟩ := D.even_of_suzukiType h (by intro h'; cases h')
  refine ⟨ℓ, hr, Or.inr (Or.inl ⟨fun hp => ?_, ⟨ℓ, h⟩, rfl⟩)⟩
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic =>
    have := ClassicalModel.hasRank_unique _ hr hp
    omega
  | orthPlus => simp [ClassicalModel.family] at hfam
  | orthMinus => simp [ClassicalModel.family] at hfam

variable {R T : Subgroup G} {g : G}

theorem MinChoice.false_of_caseC_typeA (I : Inputs74)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
    (hfam : D.family = .symplectic) (hq : 4 ≤ D.q) (hSA : SymplecticSplitA)
    (hPA : SymplecticPairA2) (hm : MinChoice D R T g) (hTA : T ⊓ A = ⊥) {t p : G} (ht : t ∈ T)
    (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) (hpn : D.HasMeasure p (choiceMeasure D R T))
    {ℓ : ℕ} (hpa : D.SuzukiType p .a ℓ) (h1 : Case1 D p) : False := by
  have hc := hm.sec3
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  have hZ : Odd (Nat.card (center ↥A)) :=
    (I.h222.conclusion D hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)).1
  have hA := hc.hyp.standard.1
  obtain ⟨k, hk⟩ := D.even_of_suzukiType hpa (by intro h; cases h)
  have hℓ0 := D.pos_of_hasRank (D.hasRank_of_suzukiType hpa)
  have hn : choiceMeasure D R T = 3 * ℓ + 2 :=
    hpn.unique (D.hasMeasure_of_suzukiType_a hpa (by omega) hfam)
  have hTA' : ¬ T ≤ A := fun h =>
    hc.T_ne_bot (by rw [← hTA]; exact (inf_eq_left.mpr h).symm)
  have hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A :=
    fun T' x h' hT' => hTA' (hm.le_of_le T' x h' hT')
  have hbetter : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ∀ s ∈ T', s ≠ 1 → ∀ q ∈ A,
      s⁻¹ * q ∈ R → ¬ Smaller D (choiceMeasure D R T) q := by
    rintro T' x h' s hs hs1 q hq hqρ ⟨m, hm', hqm⟩
    have := hm.le_of_mem h' (Or.inr hTA') hs hs1 hq hqρ hqm
    omega
  have hprim : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ∀ s ∈ T', s ≠ 1 → ∀ q ∈ A,
      s⁻¹ * q ∈ R → ¬ D.IsPrimary q := fun T' x h' s hs hs1 q hq hqρ hqp =>
    hbetter T' x h' s hs hs1 q hq hqρ ⟨3, by omega, D.hasMeasure_three_of_isPrimary hfam hqp⟩
  have hle : ∀ u ∈ T, ∀ p' ∈ A, u⁻¹ * p' ∈ R → p' ∈ jGroup A p := by
    rcases hc.case222 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy I.h222 D hq ht ht1 hp hρ with
      ⟨hle, -⟩ | hII
    · exact hle
    · exfalso
      have := hII.2.2
      omega
  obtain ⟨T', x, h', s, hs, hs1, q, hq, hqρ, hqs⟩ :
      ∃ (T' : Subgroup G) (x : G), Sec3 A R T' x ∧
        ∃ s ∈ T', s ≠ 1 ∧ ∃ q ∈ A, s⁻¹ * q ∈ R ∧ Smaller D (choiceMeasure D R T) q := by
    by_cases hℓ4 : 4 ≤ ℓ
    ·
      obtain ⟨F, _, _, ι₁, ι₂, hF, hsd⟩ := hSA G A D hfam hA hZ hq p ℓ hℓ4 hpa
      have hsd' : SplitData A (jGroup A p) (Smaller D (choiceMeasure D R T))
          (Smaller D (choiceMeasure D R T)) F ι₁ ι₂ := by
        rw [h1.1]
        exact hsd.mono
          (fun y hy => ⟨3 * 2 + 2, by omega, D.hasMeasure_of_suzukiType_a hy (by omega) hfam⟩)
          (fun y hy => ⟨3 * (ℓ - 2) + 2, by omega,
            D.hasMeasure_of_suzukiType_a hy (by omega) hfam⟩)
      exact hc.caseC_split I hZ D hle hF hsd'
        (fun b hbT hne => hc.cover_derived_sp I hTy D hfam hq hno hprim hbT hne) hno
    ·
      have hℓ : ℓ = 2 := by omega
      subst hℓ
      obtain ⟨a, haA, hcomm, hJa, hmix⟩ := hPA G A D hfam hA hZ hq p hpa
      rw [← h1.1] at hcomm hJa hmix
      obtain ⟨t₁, ht₁, ht₁1, t₂, ht₂, ht₂1, ht₁₂⟩ := hc.exists_ne_ne
      refine hc.caseC_core I hZ D hle haA hcomm hJa ht₁ ht₂ ht₁₂ ?_ ?_
        (fun hbT hne => hc.cover_derived_sp I hTy D hfam hq hno hprim hbT hne) hno
      · intro u hu hu1 p' hp' hρ'
        have hJ := hle u hu p' hp' hρ'
        have hp'1 := hc.aPart_ne_one hu hu1 hρ'
        exact ⟨3 * 2 + 1, by omega, D.hasMeasure_of_suzukiType_c (hmix _ hJ hp'1 _ hJ hp'1) hfam⟩
      · intro p₁ hp₁ hρ₁ p₂ hp₂ hρ₂
        exact ⟨3 * 2 + 1, by omega, D.hasMeasure_of_suzukiType_c (hmix _
          (hle t₂ ht₂ p₂ hp₂ hρ₂) (hc.aPart_ne_one ht₂ ht₂1 hρ₂) _ (hle t₁ ht₁ p₁ hp₁ hρ₁)
          (hc.aPart_ne_one ht₁ ht₁1 hρ₁)) hfam⟩
  exact hbetter T' x h' s hs hs1 q hq hqρ hqs

end CFSG.ComponentClassification.RankTwoClassical
