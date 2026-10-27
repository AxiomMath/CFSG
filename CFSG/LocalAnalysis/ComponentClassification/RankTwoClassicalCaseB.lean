module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalReduce

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard

namespace SplitData

variable {G : Type} [Group G] {A J : Subgroup G} {P₁ P₂ : G → Prop} {F : Type} [Field F]
  {ι₁ ι₂ : F → G} (h : SplitData A J P₁ P₂ F ι₁ ι₂)
include h

theorem mem_rightConjugate_iff {e : F} {a : G}
    (ha : ∀ x, a⁻¹ * ι₁ x * a = ι₁ x ∧ a⁻¹ * ι₂ x * a = ι₂ (e * x)) {v : G} :
    v ∈ rightConjugate J a ↔ ∃ d, v = ι₁ d * ι₂ (e * d) := by
  rw [AschbacherTightEmbedding.mem_rightConjugate_iff, h.mem_iff]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    calc v = a⁻¹ * (a * v * a⁻¹) * a := by group
      _ = (a⁻¹ * ι₁ d * a) * (a⁻¹ * ι₂ d * a) := by rw [hd]; group
      _ = ι₁ d * ι₂ (e * d) := by rw [(ha d).1, (ha d).2]
  · rintro ⟨d, rfl⟩
    refine ⟨d, ?_⟩
    calc a * (ι₁ d * ι₂ (e * d)) * a⁻¹ = a * ((a⁻¹ * ι₁ d * a) * (a⁻¹ * ι₂ d * a)) * a⁻¹ := by
          rw [(ha d).1, (ha d).2]
      _ = ι₁ d * ι₂ d := by group

theorem mem_iff_one (j : G) : j ∈ J ↔ ∃ d, j = ι₁ d * ι₂ (1 * d) := by
  simp only [one_mul]
  exact h.mem_iff j

theorem eq_zero_of_mul_eq {e e' : F} (hee : e ≠ e') {d d' : F}
    (hd : ι₁ d * ι₂ (e * d) = ι₁ d' * ι₂ (e' * d')) : d = 0 := by
  obtain ⟨rfl, h2⟩ := h.eq_of_mul_eq hd
  have h3 : (e - e') * d = 0 := by rw [sub_mul, h2, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) hee
  · exact h4

theorem mem_sup {e : F} (he : e ≠ 1) {a : G}
    (ha : ∀ x, a⁻¹ * ι₁ x * a = ι₁ x ∧ a⁻¹ * ι₂ x * a = ι₂ (e * x)) (x y : F) :
    ι₁ x * ι₂ y ∈ J ⊔ rightConjugate J a := by
  have he' : e - 1 ≠ 0 := sub_ne_zero.mpr he
  set d' := (y - x) / (e - 1) with hd'
  set d := x - d' with hd
  have h1 : ι₁ d * ι₂ d ∈ J := (h.mem_iff _).mpr ⟨d, rfl⟩
  have h2 : ι₁ d' * ι₂ (e * d') ∈ rightConjugate J a :=
    (h.mem_rightConjugate_iff ha).mpr ⟨d', rfl⟩
  have h3 : ι₁ d * ι₂ d * (ι₁ d' * ι₂ (e * d')) = ι₁ x * ι₂ y := by
    rw [h.mul_mul]
    congr 2
    · rw [hd]
      ring
    · have : (e - 1) * d' = y - x := by
        rw [hd']
        field_simp
      rw [hd]
      linear_combination this
  rw [← h3]
  exact mul_mem (mem_sup_left h1) (mem_sup_right h2)

end SplitData

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem caseB (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (D : ClassicalModel A) (hfam : D.family ≠ .symplectic) (hq : 4 ≤ D.q) (hS : ClassicalSplit)
    {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R)
    (hnp : ¬ D.IsPrimary p) {n : ℕ} (hn : D.HasMeasure p n) (hTA : T = sec3V R T ⊓ A) :
    ∃ (T' : Subgroup G) (x : G), Sec3 A R T' x ∧ T' ≤ A ∧
      ∃ s ∈ T', s ≠ 1 ∧ s ∈ A ∧ Smaller D n s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, -, -, hI⟩ := hc.case14 I hTy D hfam hq ht ht1 hp hρ
  obtain ⟨y₀, hJ⟩ := hc.exists_jData I hTy D hfam hq ht ht1 hp hρ
  have hTJ : T = jGroup A p := hTA.trans (hc.inf_sec3V_eq I.h32 I.h4 I.h34 hJ)
  have hTq : Nat.card T = D.q := by
    rw [hTJ]
    exact hc.card_jGroup I hTy D hfam hq ht ht1 hp hρ
  obtain ⟨F, _, _, ι₁, ι₂, hF, hsd⟩ := exists_splitAt_smaller hS D hfam hc.hyp.standard.1 hZ hq hp
    (hc.orderOf_aPart I.h32 ht ht1 hρ) hnp hn hI
  rw [← hTJ] at hsd
  obtain ⟨m, hm⟩ := D.exists_q_eq
  have : CharP F 2 := charP_two_of_card (k := m) (by rw [hF, hm])
  have := Fintype.ofFinite F
  have hcardF : 1 < ((Finset.univ.erase (0 : F)).erase 1).card := by
    have h1 : Fintype.card F = D.q := by rw [← Nat.card_eq_fintype_card, hF]
    rw [Finset.card_erase_of_mem (by simp), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, h1]
    omega
  obtain ⟨e₁, he₁, e₂, he₂, he₁₂⟩ := Finset.one_lt_card.mp hcardF
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at he₁ he₂
  obtain ⟨a₁, ha₁A, ha₁⟩ := hsd.scalar e₁ he₁.2
  obtain ⟨a₂, ha₂A, ha₂⟩ := hsd.scalar e₂ he₂.2
  have hTA' : T ≤ A := hTA ▸ inf_le_right
  have hTbot := hc.T_inf_conj hZ
  have hT1 : T ≠ ⊥ := hc.T_ne_bot
  have hfacts : ∀ (e : F) (a : G), e ≠ 1 →
      (∀ x, a⁻¹ * ι₁ x * a = ι₁ x ∧ a⁻¹ * ι₂ x * a = ι₂ (e * x)) →
      rightConjugate T a ≤ centralizer (T : Set G) ∧ T ⊓ rightConjugate T a = ⊥ ∧
        rightConjugate T a ≠ T ∧ rightConjugate T a ≤ A := by
    intro e a he ha
    have hcen : rightConjugate T a ≤ centralizer (T : Set G) := by
      intro v hv
      rw [mem_centralizer_iff]
      intro u hu
      obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha).mp hv
      obtain ⟨d', rfl⟩ := (hsd.mem_iff u).mp hu
      exact (hsd.commute_mul d' d' d (e * d)).eq
    have hinf : T ⊓ rightConjugate T a = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hv1, hv2⟩ := mem_inf.mp hv
      obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha).mp hv2
      obtain ⟨d', hd'⟩ := (hsd.mem_iff_one _).mp hv1
      have h0 := hsd.eq_zero_of_mul_eq he hd'
      rw [h0, mul_zero, hsd.map_zero₁, hsd.map_zero₂, mul_one]
      exact one_mem _
    refine ⟨hcen, hinf, fun heq => hT1 ?_, ?_⟩
    · rw [← inf_idem T]
      conv_lhs => rw [show T ⊓ T = T ⊓ rightConjugate T a by rw [heq]]
      exact hinf
    · intro v hv
      obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha).mp hv
      exact mul_mem (hsd.mem₁ d) (hsd.mem₂ _)
  obtain ⟨hcen₁, hinf₁, hne₁, hA₁⟩ := hfacts e₁ a₁ he₁.1 ha₁
  obtain ⟨hcen₂, hinf₂, hne₂, hA₂⟩ := hfacts e₂ a₂ he₂.1 ha₂
  have hVeq : ∀ a : G, rightConjugate T a ≤ centralizer (T : Set G) →
      T ⊓ rightConjugate T a = ⊥ → rightConjugate T a ≠ T →
        sec3V T (rightConjugate T a) = T ⊔ rightConjugate T a := by
    intro a hcen hinf hne
    have hle : T ⊔ rightConjugate T a ≤ sec3V T (rightConjugate T a) := le_sec3V_of ⟨a, rfl⟩
    refine (eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
    rw [(hc.card_derived I hTy D hfam hq hcen hne).2,
      card_sup_eq_mul (hcen.trans (centralizer_le_normalizer _)) hinf,
      rightConjugate_card, hTq]
  have hV₁ := hVeq a₁ hcen₁ hinf₁ hne₁
  have hV₂ := hVeq a₂ hcen₂ hinf₂ hne₂
  have hsup : T ⊔ rightConjugate T a₂ = T ⊔ rightConjugate T a₁ := by
    have hle : T ⊔ rightConjugate T a₂ ≤ T ⊔ rightConjugate T a₁ := by
      refine sup_le le_sup_left fun v hv => ?_
      obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha₂).mp hv
      exact hsd.mem_sup he₁.1 ha₁ d (e₂ * d)
    refine eq_of_le_of_card_ge hle ?_
    rw [card_sup_eq_mul (hcen₁.trans (centralizer_le_normalizer _)) hinf₁,
      card_sup_eq_mul (hcen₂.trans (centralizer_le_normalizer _)) hinf₂, rightConjugate_card,
      rightConjugate_card]
  have hcov : ∃ a : G, rightConjugate T a ≤ T ⊔ rightConjugate T a₁ ∧
      sec3V T (rightConjugate T a) = T ⊔ rightConjugate T a₁ ∧
      ∀ v ∈ sec3V T (rightConjugate T a), v ∉ rightConjugate A g →
        ∃ y : G, rightConjugate T y ≤ sec3V T (rightConjugate T a) ∧ v ∈ rightConjugate T y := by
    rcases hc.cover_derived I hTy D hfam hq hcen₁ hne₁ with h1 | h1
    · rcases hc.cover_derived I hTy D hfam hq hcen₂ hne₂ with h2 | h2
      · exfalso
        have heq : rightConjugate T a₁ = rightConjugate T a₂ := by
          rw [h1, h2, hV₁, hV₂, hsup]
        have h12 : rightConjugate T a₁ = ⊥ := by
          rw [eq_bot_iff]
          intro v hv
          have hv2 : v ∈ rightConjugate T a₂ := heq ▸ hv
          obtain ⟨d, rfl⟩ := (hsd.mem_rightConjugate_iff ha₁).mp hv
          obtain ⟨d', hd'⟩ := (hsd.mem_rightConjugate_iff ha₂).mp hv2
          rw [hsd.eq_zero_of_mul_eq he₁₂ hd', mul_zero, hsd.map_zero₁, hsd.map_zero₂, mul_one]
          exact one_mem _
        have hc1 := rightConjugate_card T a₁
        rw [h12, card_bot, hTq] at hc1
        omega
      · exact ⟨a₂, hsup ▸ le_sup_right, hV₂.trans hsup, h2⟩
    · exact ⟨a₁, le_sup_right, hV₁, h1⟩
  obtain ⟨a, -, hVa, hcover⟩ := hcov
  have hout : ∃ v : G, v ∉ rightConjugate A g ∧ v ∈ T ⊔ rightConjugate T a₁ ∧ v ≠ 1 ∧
      Smaller D n v ∧ v ^ 2 = 1 := by
    by_contra hno
    push Not at hno
    apply hT1
    rw [eq_bot_iff, ← hTbot]
    intro j hj
    refine mem_inf.mpr ⟨hj, ?_⟩
    obtain ⟨d, rfl⟩ := (hsd.mem_iff j).mp hj
    have h1 : ∀ x : F, ι₁ x ∈ rightConjugate A g := by
      intro x
      by_cases hx : x = 0
      · rw [hx, hsd.map_zero₁]
        exact one_mem _
      by_contra hx'
      have hmem : ι₁ x ∈ T ⊔ rightConjugate T a₁ := by
        have := hsd.mem_sup he₁.1 ha₁ x 0
        rwa [hsd.map_zero₂, mul_one] at this
      exact hno (ι₁ x) hx' hmem (hsd.ne_one₁ hx) (hsd.prop₁ x hx) (by rw [sq, hsd.mul_self₁])
    have h2 : ∀ x : F, ι₂ x ∈ rightConjugate A g := by
      intro x
      by_cases hx : x = 0
      · rw [hx, hsd.map_zero₂]
        exact one_mem _
      by_contra hx'
      have hmem : ι₂ x ∈ T ⊔ rightConjugate T a₁ := by
        have := hsd.mem_sup he₁.1 ha₁ 0 x
        rwa [hsd.map_zero₁, one_mul] at this
      exact hno (ι₂ x) hx' hmem (hsd.ne_one₂ hx) (hsd.prop₂ x hx) (by rw [sq, hsd.mul_self₂])
    exact mul_mem (h1 d) (h2 d)
  obtain ⟨v, hvA, hvV, hv1, hvs, hv2⟩ := hout
  have hvV' : v ∈ sec3V T (rightConjugate T a) := by
    rw [hVa]
    exact hvV
  obtain ⟨y, hyV, hvy⟩ := hcover v hvV' hvA
  have hyA : rightConjugate T y ≤ A := by
    rw [hVa] at hyV
    exact hyV.trans (sup_le hTA' hA₁)
  obtain ⟨w, hw⟩ := hc.exists_conj
  have hRT : rightConjugate T y = rightConjugate R (w * y) := by rw [hw, rightConjugate_mul]
  have hyR : rightConjugate T y ≤ centralizer (R : Set G) := by
    intro u hu
    rw [mem_centralizer_iff]
    intro r hr
    exact (hc.commute_of_mem (hyA hu) hr).eq.symm
  have hvA' : v ∈ A := hyA hvy
  refine ⟨rightConjugate T y, w * y, ?_, hyA, v, hvy, hv1, hvA', hvs⟩
  rw [hRT] at hyR hvy ⊢
  exact sec3_of_conj hc.hyp hc.sylowR hZ hyR hvy hvA' (by rw [inv_mul_cancel]; exact one_mem _)
    hv1 hv2

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
