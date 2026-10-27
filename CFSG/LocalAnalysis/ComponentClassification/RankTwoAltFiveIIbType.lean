module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbLocal

public section

open Subgroup Equiv CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

theorem b₀_cycle {b₀ : G} (hb₀N : b₀ ∈ normalizer (V₀ : Set G)) (hb₀3 : orderOf b₀ = 3)
    (hb₀tr : ∀ b ∈ V₀, ∀ c ∈ V₀, b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (b₀ ^ k)⁻¹ * b * b₀ ^ k = c)
    {w : G} (hw : w ∈ V₀) (hw1 : w ≠ 1) :
    b₀ * w * b₀⁻¹ ≠ w ∧ b₀ * (b₀ * w * b₀⁻¹) * b₀⁻¹ = w * (b₀ * w * b₀⁻¹) := by
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  have hconj : ∀ {u y : G}, u ∈ normalizer (V₀ : Set G) → y ∈ V₀ → u * y * u⁻¹ ∈ V₀ :=
    fun hu hy => (mem_normalizer_iff.mp hu _).mp hy
  have hb₀3' : b₀ ^ 3 = 1 := by rw [← hb₀3]; exact pow_orderOf_eq_one b₀
  have hfix : ∀ y ∈ V₀, y ≠ 1 → b₀ * y * b₀⁻¹ ≠ y := by
    intro y hy hy1 hfy
    have hpow : ∀ k : ℕ, (b₀ ^ k)⁻¹ * y * b₀ ^ k = y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e : b₀⁻¹ * y * b₀ = y := by
          calc b₀⁻¹ * y * b₀ = b₀⁻¹ * (b₀ * y * b₀⁻¹) * b₀ := by rw [hfy]
            _ = y := by group
        calc (b₀ ^ (k + 1))⁻¹ * y * b₀ ^ (k + 1) = b₀⁻¹ * ((b₀ ^ k)⁻¹ * y * b₀ ^ k) * b₀ := by
              rw [pow_succ]; group
          _ = y := by rw [ih, e]
    obtain ⟨y', hy', hy'1, hy'y⟩ := exists_ne_one_ne h.card_V₀ hV₀2 hy
    obtain ⟨k, hk⟩ := hb₀tr y hy y' hy' hy1 hy'1
    exact hy'y (by rw [← hk, hpow k])
  refine ⟨hfix w hw hw1, ?_⟩
  set u := b₀ * w * b₀⁻¹ with hu
  have huV₀ : u ∈ V₀ := hconj hb₀N hw
  have hu1 : u ≠ 1 := fun h1 => hw1 (by
    calc w = b₀⁻¹ * u * b₀ := by rw [hu]; group
      _ = 1 := by rw [h1]; group)
  have huw : u ≠ w := hfix w hw hw1
  set u' := b₀ * u * b₀⁻¹ with hu'
  have hu'V₀ : u' ∈ V₀ := hconj hb₀N huV₀
  have hu'1 : u' ≠ 1 := fun h1 => hu1 (by
    calc u = b₀⁻¹ * u' * b₀ := by rw [hu']; group
      _ = 1 := by rw [h1]; group)
  have hu'u : u' ≠ u := hfix u huV₀ hu1
  have hu'w : u' ≠ w := by
    intro he
    have h3 : b₀ * b₀ * b₀ = 1 := by rw [← pow_three', hb₀3']
    have hbinv : b₀⁻¹ = b₀ * b₀ := by
      calc b₀⁻¹ = b₀⁻¹ * (b₀ * b₀ * b₀) := by rw [h3, mul_one]
        _ = b₀ * b₀ := by group
    apply huw
    calc u = b₀⁻¹ * u' * b₀ := by rw [hu', hu]; group
      _ = b₀⁻¹ * w * b₀ := by rw [he]
      _ = (b₀ * b₀) * w * (b₀ * b₀)⁻¹ := by rw [← hbinv, inv_inv]
      _ = u' := by rw [hu', hu]; group
      _ = w := he
  rcases mem_four h.card_V₀ hV₀2 hw huV₀ hw1 hu1 huw.symm hu'V₀ with h1 | h1 | h1 | h1
  · exact absurd h1 hu'1
  · exact absurd h1 hu'w
  · exact absurd h1 hu'u
  · exact h1

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem exists_b : ∃ b₀ b : G, b₀ ∈ normalizer (V₀ : Set G) ∧ orderOf b₀ = 3 ∧
    (∀ c ∈ V₀, ∀ d ∈ V₀, c ≠ 1 → d ≠ 1 → ∃ k : ℕ, (b₀ ^ k)⁻¹ * c * b₀ ^ k = d) ∧
    b ∈ normalizer (P : Set G) ∧ b ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) ∧
    (∀ w ∈ V₀, b * w * b⁻¹ = b₀ * w * b₀⁻¹) ∧
    ∀ y ∈ P, ∀ r ∈ R, ⁅b * y * b⁻¹, r⁆ = b₀ * ⁅y, r⁆ * b₀⁻¹ := by
  obtain ⟨eA⟩ := h.equiv
  obtain ⟨b₀, hb₀A, hb₀N, hb₀3, hb₀tr, -⟩ := exists_klein_three eA h.V₀_le_A h.card_V₀
  have hb₀R : b₀ ∈ centralizer (R : Set G) := le_centralizer_iff.mp h.sylowR.le hb₀A
  have hb₀V := h.mem_normalizer_V (centralizer_le_normalizer _ hb₀R) hb₀N
  obtain ⟨p, hp, hpb⟩ := exists_mul_mem_normalizer hP (h.le_normalizer_transvGroup hb₀V)
  obtain ⟨hpV, hpC, hpmod⟩ := mem_transvGroup.mp hp
  have hpinv := inv_mem hp
  obtain ⟨-, -, hpmod'⟩ := mem_transvGroup.mp hpinv
  have hbw : ∀ w ∈ V₀, p * b₀ * w * (p * b₀)⁻¹ = b₀ * w * b₀⁻¹ := by
    intro w hw
    have hw' : b₀ * w * b₀⁻¹ ∈ V₀ := (mem_normalizer_iff.mp hb₀N w).mp hw
    have hpw : p * (b₀ * w * b₀⁻¹) = (b₀ * w * b₀⁻¹) * p := (mem_centralizer_iff.mp hpC _ hw').symm
    calc p * b₀ * w * (p * b₀)⁻¹ = p * (b₀ * w * b₀⁻¹) * p⁻¹ := by group
      _ = b₀ * w * b₀⁻¹ := by rw [hpw]; group
  refine ⟨b₀, p * b₀, hb₀N, hb₀3, hb₀tr, hpb, mul_mem hpV hb₀V, hbw, fun y hy r hr => ?_⟩
  have hw₁ := hpmod' r (mem_sup_left hr)
  set w₁ := r⁻¹ * (p⁻¹ * r * p⁻¹⁻¹) with hw₁def
  have hw₂ : b₀⁻¹ * w₁ * b₀ ∈ V₀ := by
    have := (mem_normalizer_iff.mp (inv_mem hb₀N) w₁).mp hw₁
    rwa [inv_inv] at this
  have hb₀r : b₀ * r = r * b₀ := (mem_centralizer_iff.mp hb₀R r hr).symm
  have hs : (p * b₀)⁻¹ * r * (p * b₀) = r * (b₀⁻¹ * w₁ * b₀) := by
    have e1 : p⁻¹ * r * p = r * w₁ := by rw [hw₁def]; group
    calc (p * b₀)⁻¹ * r * (p * b₀) = b₀⁻¹ * (p⁻¹ * r * p) * b₀ := by group
      _ = b₀⁻¹ * (r * w₁) * b₀ := by rw [e1]
      _ = b₀⁻¹ * r * b₀ * (b₀⁻¹ * w₁ * b₀) := by group
      _ = r * (b₀⁻¹ * w₁ * b₀) := by
          rw [show b₀⁻¹ * r * b₀ = r by
            calc b₀⁻¹ * r * b₀ = b₀⁻¹ * (r * b₀) := by group
              _ = b₀⁻¹ * (b₀ * r) := by rw [hb₀r]
              _ = r := by group]
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hw₂P : b₀⁻¹ * w₁ * b₀ ∈ P := hVP (h.V₀_le hw₂)
  have hyw : ⁅y, b₀⁻¹ * w₁ * b₀⁆ = 1 := by
    rw [commutatorElement_def, P_comm_V₀ hP hw₂ hy]
    group
  have hc := h.commP_mul_right hP hPC hy hrP hw₂P
  rw [hyw, mul_one] at hc
  have hcV₀ := h.commP_mem hP hPC hy hrP
  calc ⁅p * b₀ * y * (p * b₀)⁻¹, r⁆ =
      p * b₀ * ⁅y, (p * b₀)⁻¹ * r * (p * b₀)⁆ * (p * b₀)⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = p * b₀ * ⁅y, r⁆ * (p * b₀)⁻¹ := by rw [hs, hc]
    _ = b₀ * ⁅y, r⁆ * b₀⁻¹ := hbw _ hcV₀

theorem inv_mul_b_conj_not_mem {b₀ b : G} (hb₀N : b₀ ∈ normalizer (V₀ : Set G))
    (hb₀3 : orderOf b₀ = 3)
    (hb₀tr : ∀ c ∈ V₀, ∀ d ∈ V₀, c ≠ 1 → d ≠ 1 → ∃ k : ℕ, (b₀ ^ k)⁻¹ * c * b₀ ^ k = d)
    (hbP : b ∈ normalizer (P : Set G))
    (hbc : ∀ y ∈ P, ∀ r ∈ R, ⁅b * y * b⁻¹, r⁆ = b₀ * ⁅y, r⁆ * b₀⁻¹)
    {c : G} (hc : c ∈ P) (hcV : c ∉ R ⊔ T) : c⁻¹ * (b * c * b⁻¹) ∉ R ⊔ T := by
  intro hv
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  obtain ⟨r, hr, hr1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hbcP : b * c * b⁻¹ ∈ P := (mem_normalizer_iff.mp hbP c).mp hc
  have hvP : c⁻¹ * (b * c * b⁻¹) ∈ P := mul_mem (inv_mem hc) hbcP
  have h1 : ⁅b * c * b⁻¹, r⁆ = ⁅c, r⁆ := by
    have e : b * c * b⁻¹ = c * (c⁻¹ * (b * c * b⁻¹)) := by group
    rw [e, h.commP_mul_left hP hPC hc hvP hrP]
    have hvr : ⁅c⁻¹ * (b * c * b⁻¹), r⁆ = 1 := by
      rw [commutatorElement_def, h.comm hv (mem_sup_left hr)]
      group
    rw [hvr, mul_one]
  rw [hbc c hc r hr] at h1
  have hcr := h.commP_mem hP hPC hc hrP
  have hcr1 : ⁅c, r⁆ ≠ 1 := fun he => hr1 (by
    have := h.mem_V₀_of_commP_eq_one hP hPC hc hcV (mem_sup_left hr) he
    have h2 : r ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr, this⟩
    rwa [h.inf_R_V₀, mem_bot] at h2)
  exact (h.b₀_cycle hb₀N hb₀3 hb₀tr hcr hcr1).1 h1

theorem mem_cosets {c₁ c₂ : G} (hc₁ : c₁ ∈ P) (hc₁V : c₁ ∉ R ⊔ T) (hc₂ : c₂ ∈ P)
    (hc₂V : c₂ ∉ R ⊔ T) (hc₁₂ : c₁⁻¹ * c₂ ∉ R ⊔ T) {x : G} (hx : x ∈ P) :
    x ∈ R ⊔ T ∨ c₁⁻¹ * x ∈ R ⊔ T ∨ c₂⁻¹ * x ∈ R ⊔ T ∨ (c₁ * c₂)⁻¹ * x ∈ R ⊔ T := by
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  obtain ⟨r, hr, hr1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hrV₀ : r ∉ V₀ := fun h0 => hr1 (by
    have h2 : r ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr, h0⟩
    rwa [h.inf_R_V₀, mem_bot] at h2)
  have hker : ∀ y ∈ P, ⁅y, r⁆ = 1 → y ∈ R ⊔ T := fun y hy he => by
    by_contra hyV
    exact hrV₀ (h.mem_V₀_of_commP_eq_one hP hPC hy hyV (mem_sup_left hr) he)
  have hinv : ∀ y ∈ P, ⁅y⁻¹, r⁆ = ⁅y, r⁆ := by
    intro y hy
    have h1 := h.commP_mul_left hP hPC (inv_mem hy) hy hrP
    rw [inv_mul_cancel, commutatorElement_one_left] at h1
    have h2 := hV₀2 _ (h.commP_mem hP hPC hy hrP)
    calc ⁅y⁻¹, r⁆ = ⁅y⁻¹, r⁆ * (⁅y, r⁆ * ⁅y, r⁆) := by rw [h2, mul_one]
      _ = ⁅y, r⁆ := by rw [← mul_assoc, ← h1, one_mul]
  have hdiff : ∀ {y y' : G}, y ∈ P → y' ∈ P → ⁅y, r⁆ = ⁅y', r⁆ → y⁻¹ * y' ∈ R ⊔ T := by
    intro y y' hy hy' he
    apply hker _ (mul_mem (inv_mem hy) hy')
    rw [h.commP_mul_left hP hPC (inv_mem hy) hy' hrP, hinv y hy, he]
    exact hV₀2 _ (h.commP_mem hP hPC hy' hrP)
  have hf₁ := h.commP_mem hP hPC hc₁ hrP
  have hf₂ := h.commP_mem hP hPC hc₂ hrP
  have hfx := h.commP_mem hP hPC hx hrP
  have hf₁1 : ⁅c₁, r⁆ ≠ 1 := fun he => hc₁V (hker _ hc₁ he)
  have hf₂1 : ⁅c₂, r⁆ ≠ 1 := fun he => hc₂V (hker _ hc₂ he)
  have hf₁₂ : ⁅c₁, r⁆ ≠ ⁅c₂, r⁆ := fun he => hc₁₂ (hdiff hc₁ hc₂ he)
  rcases mem_four h.card_V₀ hV₀2 hf₁ hf₂ hf₁1 hf₂1 hf₁₂ hfx with h1 | h1 | h1 | h1
  · exact Or.inl (hker _ hx h1)
  · exact Or.inr (Or.inl (hdiff hc₁ hx h1.symm))
  · exact Or.inr (Or.inr (Or.inl (hdiff hc₂ hx h1.symm)))
  · refine Or.inr (Or.inr (Or.inr (hdiff (mul_mem hc₁ hc₂) hx ?_)))
    rw [h.commP_mul_left hP hPC hc₁ hc₂ hrP, h1]

theorem exists_isVprime_of_comm (hP64 : Nat.card P = 64) {c₁ c₂ : G} (hc₁ : c₁ ∈ P)
    (hc₁V : c₁ ∉ R ⊔ T) (hc₁2 : c₁ * c₁ = 1) (hc₂ : c₂ ∈ P) (hc₂V : c₂ ∉ R ⊔ T)
    (hc₂2 : c₂ * c₂ = 1) (hc₁₂ : c₁⁻¹ * c₂ ∉ R ⊔ T) (hcomm : c₁ * c₂ = c₂ * c₁) :
    ∃ V' : Subgroup G, IsVprime (R ⊔ T) V₀ P V' := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hc₁i : c₁⁻¹ = c₁ := inv_eq_of_mul_eq_one_right hc₁2
  have hc₃ : c₁ * c₂ ∈ P := mul_mem hc₁ hc₂
  have hc₃2 : c₁ * c₂ * (c₁ * c₂) = 1 := by
    calc c₁ * c₂ * (c₁ * c₂) = c₁ * (c₂ * c₁) * c₂ := by group
      _ = c₁ * (c₁ * c₂) * c₂ := by rw [hcomm]
      _ = (c₁ * c₁) * (c₂ * c₂) := by group
      _ = 1 := by rw [hc₁2, hc₂2, one_mul]
  have hc₃V : c₁ * c₂ ∉ R ⊔ T := fun he => hc₁₂ (by rwa [hc₁i])
  have hform : ∀ d ∈ P, d ∉ R ⊔ T → d * d = 1 →
      ∃ c : G, (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) ∧ c⁻¹ * d ∈ V₀ := by
    intro d hd hdV hd2
    have key : ∀ c : G, c ∈ P → c ∉ R ⊔ T → c * c = 1 → c⁻¹ * d ∈ R ⊔ T → c⁻¹ * d ∈ V₀ := by
      intro c hc hcV hc2 hcd
      refine h.P_invol_coset hP hPC hc hcV hc2 hcd ?_
      rwa [mul_inv_cancel_left]
    rcases h.mem_cosets hP hPC hc₁ hc₁V hc₂ hc₂V hc₁₂ hd with h1 | h1 | h1 | h1
    · exact absurd h1 hdV
    · exact ⟨c₁, Or.inl rfl, key c₁ hc₁ hc₁V hc₁2 h1⟩
    · exact ⟨c₂, Or.inr (Or.inl rfl), key c₂ hc₂ hc₂V hc₂2 h1⟩
    · exact ⟨c₁ * c₂, Or.inr (Or.inr rfl), key _ hc₃ hc₃V hc₃2 h1⟩
  have h12 : Commute c₁ c₂ := hcomm
  have hk₁ : ∀ c : G, (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) → Commute c c₁ := by
    rintro c (rfl | rfl | rfl)
    · exact Commute.refl _
    · exact h12.symm
    · exact (Commute.refl c₁).mul_left h12.symm
  have hk₂ : ∀ c : G, (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) → Commute c c₂ := by
    rintro c (rfl | rfl | rfl)
    · exact h12
    · exact Commute.refl _
    · exact h12.mul_left (Commute.refl c₂)
  have hpair : ∀ c c' : G, (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) →
      (c' = c₁ ∨ c' = c₂ ∨ c' = c₁ * c₂) → c * c' = c' * c := by
    intro c c' hc hc'
    rcases hc' with rfl | rfl | rfl
    · exact (hk₁ c hc).eq
    · exact (hk₂ c hc).eq
    · exact ((hk₁ c hc).mul_right (hk₂ c hc)).eq
  have hcomm' : ∀ {d d' : G}, d ∈ P → d ∉ R ⊔ T → d * d = 1 → d' ∈ P → d' ∉ R ⊔ T →
      d' * d' = 1 → d * d' = d' * d := by
    intro d d' hd hdV hd2 hd' hd'V hd'2
    obtain ⟨c, hc, hcw⟩ := hform d hd hdV hd2
    obtain ⟨c', hc', hc'w⟩ := hform d' hd' hd'V hd'2
    set w := c⁻¹ * d with hw
    set w' := c'⁻¹ * d' with hw'
    have hdc : d = c * w := by rw [hw]; group
    have hd'c : d' = c' * w' := by rw [hw']; group
    have hcP : c ∈ P := by rcases hc with rfl | rfl | rfl <;> assumption
    have hc'P : c' ∈ P := by rcases hc' with rfl | rfl | rfl <;> assumption
    have hcc' := hpair c c' hc hc'
    have hwc' : w * c' = c' * w := (P_comm_V₀ hP hcw hc'P).symm
    have hw'c : w' * c = c * w' := (P_comm_V₀ hP hc'w hcP).symm
    have hww' : w * w' = w' * w := h.comm (h.V₀_le hcw) (h.V₀_le hc'w)
    rw [hdc, hd'c]
    calc c * w * (c' * w') = c * (w * c') * w' := by group
      _ = c * (c' * w) * w' := by rw [hwc']
      _ = (c * c') * (w * w') := by group
      _ = (c' * c) * (w' * w) := by rw [hcc', hww']
      _ = c' * (c * w') * w := by group
      _ = c' * (w' * c) * w := by rw [← hw'c]
      _ = c' * w' * (c * w) := by group
  obtain ⟨V', hV'P, hV'e, hV'16, hinf, hsup, hV'inv, -⟩ :=
    h.exists_Vprime_of_comm hP hPC hP64 hVP hcomm'
  exact ⟨V', ⟨hV'P, hV'e, hV'16, hinf, hsup, hV'inv⟩⟩

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
