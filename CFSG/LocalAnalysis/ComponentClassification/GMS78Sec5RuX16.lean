module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuX16Iso
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuX17Odd
public import Certificates.Certificate15095
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModel

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS RuSModel

namespace RuSModel

theorem s0_fix : ∀ d ∈ s0List, ∀ t : Fin 8, t.val < 4 → linApply (dCode d) t = t := by decide

theorem fin8_split : ∀ t : Fin 8, t = fin8Of (4 * (t.val / 4)) ^^^ fin8Of (t.val % 4) := by decide

theorem fin8Of_mod_lt (t : Fin 8) : (fin8Of (t.val % 4)).val < 4 := by
  simp only [fin8Of]; omega

theorem code_fix_s0 : ∀ r ∈ glList, r.1 = 1 → r.2.1 = 2 → ∃ d ∈ s0List, r = dCode d := by
  decide +kernel

theorem fin8_eq_of_xor : ∀ a b s : Fin 8, (a = 0 ∨ a = 4) → (b = 0 ∨ b = 4) → s.val < 4 →
    b = a ^^^ s → a = b ∧ s = 0 := by decide

theorem fin8_xor_four : ∀ t : Fin 8, 4 ≤ t.val → (4 ^^^ t).val < 4 := by decide

theorem gl_of_pair_check : ∀ s₁ s₂ : Fin 8, s₁.val < 4 → s₂.val < 4 → s₁ ≠ 0 → s₂ ≠ 0 →
    s₁ ≠ s₂ → ∃ r ∈ glList, r = ((s₁, s₂, 4) : Lin8) := by decide +kernel

theorem gl_of_pair {s₁ s₂ : Fin 8} (h₁ : s₁.val < 4) (h₂ : s₂.val < 4) (h₁₀ : s₁ ≠ 0)
    (h₂₀ : s₂ ≠ 0) (h₁₂ : s₁ ≠ s₂) : ((s₁, s₂, 4) : Lin8) ∈ glList := by
  obtain ⟨r, hr, rfl⟩ := gl_of_pair_check s₁ s₂ h₁ h₂ h₁₀ h₂₀ h₁₂
  exact hr

theorem gl_to_pair : ∀ s₁ s₂ : Fin 8, s₁ ≠ 0 → s₂ ≠ 0 → s₁ ≠ s₂ →
    ∃ r ∈ glList, linApply r s₁ = 1 ∧ linApply r s₂ = 2 := by decide +kernel

theorem fin8_lt_four : ∀ t : Fin 8, t.val < 4 → t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 1 ^^^ 2 := by decide

theorem nodup_four : ∀ s₁ s₂ : Fin 8, s₁ ≠ 0 → s₂ ≠ 0 → s₁ ≠ s₂ → [0, s₁, s₂, s₁ ^^^ s₂].Nodup := by
  decide

theorem lt_four_of_pair : ∀ r : Lin8, ∀ s₁ s₂ : Fin 8, linApply r s₁ = 1 → linApply r s₂ = 2 →
    ∀ t : Fin 8, (t = 0 ∨ t = s₁ ∨ t = s₂ ∨ t = s₁ ^^^ s₂) → (linApply r t).val < 4 := by
  intro r s₁ s₂ h₁ h₂ t ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [RuSimCode.linApply_zero]; decide
  · rw [h₁]; decide
  · rw [h₂]; decide
  · rw [RuSimCode.linApply_xor, h₁, h₂]; decide

theorem sMul_zero_right (ε : Bool) (c : ℕ) (t s : Fin 8) (d : Fin 8) :
    sMul ε (c, t, d) (0, s, 0) = (c, t ^^^ linApply (dCode d) s, d) := by
  simp only [sMul, dPart_zero, gam_zero_right, dOvf_zero_right, dMul_zero_right, Nat.xor_zero,
    Bool.and_false, Bool.false_eq_true, ite_false, RuSimCode.fin8_xor_zero]

theorem sMul_zero_zero (ε : Bool) : sMul ε (0, 0, 0) (0, 0, 0) = (0, 0, 0) := by
  cases ε <;> decide

end RuSModel

namespace Sec3.SzR.SModel

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8} {ε : Bool}
  {Φ : ℕ × Fin 8 × Fin 8 → G} (hΦ : SModel L T R μ ν ε Φ)
include hΦ

theorem one : Φ (0, 0, 0) = 1 := by
  have := hΦ.mul (0, 0, 0) (0, 0, 0)
  rw [sMul_zero_zero] at this
  exact mul_eq_left.mp this.symm

theorem mul_zero {c : ℕ} {t s d : Fin 8} (hs : linApply (dCode d) s = s) :
    Φ (c, t ^^^ s, d) = Φ (c, t, d) * Φ (0, s, 0) := by
  rw [← hΦ.mul, sMul_zero_right, hs]

end Sec3.SzR.SModel

namespace Sec3.SzR

variable {G : Type} [Group G] {L T R : Subgroup G} {y d : G} {μ : G → ℕ} {ν : G → Fin 8}
  {ε : Bool} {Φ : ℕ × Fin 8 × Fin 8 → G} {F₁ : Subgroup G}

theorem normal_subgroupOf_centralizer :
    (F₁.subgroupOf (centralizer (F₁ : Set G))).Normal := by
  refine ⟨fun n hn c => ?_⟩
  have h1 : (n : G) * c = c * n := mem_centralizer_iff.mp c.2 _ hn
  have hc : (c : G) * n * (c : G)⁻¹ = n := by rw [← h1]; group
  show ((c * n * c⁻¹ : centralizer (F₁ : Set G)) : G) ∈ F₁
  simp only [coe_mul, coe_inv, hc]
  exact hn

section Model

variable (hM : MaskCoords L T R μ ν) (hΦ : SModel L T R μ ν ε Φ)
  (hF₁ : ∀ b, b ∈ F₁ ↔ b ∈ gmsA L T ∧ (ν b).val < 4)
include hM hΦ hF₁

theorem lift16_mem_centralizer (p : ℕ) : Φ (lift16 p) ∈ centralizer (F₁ : Set G) := by
  refine mem_centralizer_iff.mpr fun b hb => ?_
  obtain ⟨hbA, hb4⟩ := (hF₁ b).mp hb
  have h1 : Φ (lift16 p) * b * (Φ (lift16 p))⁻¹ = b :=
    hM.eq_of_ν_eq (hM.normA _ (hΦ.mem _) b hbA) hbA (by
      rw [hΦ.code _ b hbA, s0_fix _ (lift16_snd_mem p) _ hb4])
  calc b * Φ (lift16 p) = Φ (lift16 p) * b * (Φ (lift16 p))⁻¹ * Φ (lift16 p) := by rw [h1]
    _ = Φ (lift16 p) * b := by group

omit hM in
theorem zero_mem_F₁ {s : Fin 8} (hs : s.val < 4) : Φ (0, s, 0) ∈ F₁ :=
  (hF₁ _).mpr ⟨hΦ.mem_A s, by rw [hΦ.ν_eq]; exact hs⟩

theorem eq_zero_of_mem_F₁ {k : G} (hk : k ∈ F₁) : ∃ s : Fin 8, s.val < 4 ∧ Φ (0, s, 0) = k := by
  obtain ⟨hkA, hk4⟩ := (hF₁ k).mp hk
  exact ⟨ν k, hk4, hM.eq_of_ν_eq (hΦ.mem_A _) hkA (hΦ.ν_eq _)⟩

omit hM in
theorem eq_lift16_mul {r : ℕ × Fin 8 × Fin 8} (hr : r.1 < 256) (hd : r.2.2 ∈ s0List) :
    ∃ k ∈ F₁, Φ r = Φ (lift16 (enc16 r)) * k := by
  obtain ⟨c, t, d⟩ := r
  refine ⟨Φ (0, fin8Of (t.val % 4), 0), zero_mem_F₁ hΦ hF₁ (fin8Of_mod_lt t), ?_⟩
  rw [lift16_enc16 hr hd, ← hΦ.mul_zero (s0_fix _ hd _ (fin8Of_mod_lt t)), ← fin8_split t]

end Model

section Main

variable [Finite G]

theorem mem_normalizer_gmsA_of_conj (hM : MaskCoords L T R μ ν)
    (hF₁ : ∀ b, b ∈ F₁ ↔ b ∈ gmsA L T ∧ (ν b).val < 4) {f₀ : G} (hf₀A : f₀ ∈ gmsA L T)
    (hf₀ : ν f₀ = 4) {c : G} (hcF : c ∈ centralizer (F₁ : Set G))
    (hcf : c⁻¹ * f₀ * c ∈ gmsA L T) : c ∈ normalizer (gmsA L T : Set G) := by
  have hinv : c⁻¹ ∈ normalizer (gmsA L T : Set G) := by
    refine mem_normalizer_of_conj_mem_of_finite fun b hb => ?_
    rw [inv_inv]
    have hfix : ∀ b' ∈ F₁, c⁻¹ * b' * c = b' := fun b' hb' => by
      calc c⁻¹ * b' * c = c⁻¹ * (b' * c) := by group
        _ = c⁻¹ * (c * b') := by rw [mem_centralizer_iff.mp hcF b' hb']
        _ = b' := by group
    by_cases h4 : (ν b).val < 4
    · rw [hfix b ((hF₁ b).mpr ⟨hb, h4⟩)]
      exact hb
    · have hb'A : f₀⁻¹ * b ∈ gmsA L T := mul_mem (inv_mem hf₀A) hb
      have hb'F : f₀⁻¹ * b ∈ F₁ := by
        refine (hF₁ _).mpr ⟨hb'A, ?_⟩
        rw [hM.ν_mul _ (inv_mem hf₀A) _ hb, hM.ν_inv hf₀A, hf₀]
        exact fin8_xor_four _ (by omega)
      rw [show c⁻¹ * b * c = (c⁻¹ * f₀ * c) * (c⁻¹ * (f₀⁻¹ * b) * c) by group, hfix _ hb'F]
      exact mul_mem hcf hb'A
  simpa using inv_mem hinv

theorem centralizer_le_normalizer_of_codes
    (hS : SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hM : MaskCoords L T R μ ν) (hΦ : SModel L T R μ ν ε Φ)
    (hNA : normalizer (gmsA L T : Set G) ≤ normalizer (R : Set G))
    (hF₁ : ∀ b, b ∈ F₁ ↔ b ∈ gmsA L T ∧ (ν b).val < 4) :
    centralizer (F₁ : Set G) ≤ normalizer (R : Set G) := by
  classical
  have := normal_subgroupOf_centralizer (F₁ := F₁)
  set C := centralizer (F₁ : Set G) with hCdef
  have hC : ∀ p, Φ (lift16 p) ∈ C := lift16_mem_centralizer hM hΦ hF₁
  set π := QuotientGroup.mk' (F₁.subgroupOf C) with hπdef
  have hπ : ∀ a b : C, π a = π b ↔ (a : G)⁻¹ * b ∈ F₁ := fun a b => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    rfl
  set φ : ℕ → C ⧸ F₁.subgroupOf C := fun p => π ⟨Φ (lift16 p), hC p⟩ with hφdef
  have hl256 : lift16 256 = (0, 4, 0) := by decide
  set f₀ := Φ (0, 4, 0) with hf₀def
  have hf₀A : f₀ ∈ gmsA L T := hΦ.mem_A 4
  have hf₀ν : ν f₀ = 4 := hΦ.ν_eq 4
  have hf₀C : f₀ ∈ C := by rw [hf₀def, ← hl256]; exact hC 256
  have hφ256 : φ 256 = π ⟨f₀, hf₀C⟩ := by simp only [hφdef, hl256]; rfl
  have hchk : check16 ε = true := by
    cases ε
    · exact Certificates.certificate15095.1
    · exact Certificates.certificate15095.2.1
  obtain ⟨-, -, -, -, hC5⟩ := check16_spec hchk
  have hfix : ∀ c : C, π c * φ 256 = φ 256 * π c → (c : G) ∈ normalizer (R : Set G) := by
    intro c hc
    rw [hφ256, ← map_mul, ← map_mul, hπ] at hc
    refine hNA (mem_normalizer_gmsA_of_conj hM hF₁ hf₀A hf₀ν c.2 ?_)
    have hk : f₀⁻¹ * ((c : G)⁻¹ * f₀ * c) ∈ gmsA L T := by
      have := ((hF₁ _).mp hc).1
      simpa [mul_assoc] using this
    rw [show (c : G)⁻¹ * f₀ * c = f₀ * (f₀⁻¹ * ((c : G)⁻¹ * f₀ * c)) by group]
    exact mul_mem hf₀A hk
  have hmul : ∀ p q, φ (mul16 ε p q) = φ p * φ q := by
    intro p q
    set r := sMul ε (lift16 p) (lift16 q) with hr
    obtain ⟨k, hkF, hk⟩ := eq_lift16_mul hΦ hF₁ (sMul_fst_lt ε (lift16_fst_lt p) _)
      (dMul_mem_s0 _ (lift16_snd_mem p) _ (lift16_snd_mem q))
    simp only [hφdef]
    rw [← map_mul, hπ, mul16_eq]
    show (Φ (lift16 (enc16 r)))⁻¹ * (Φ (lift16 p) * Φ (lift16 q)) ∈ F₁
    rw [← hΦ.mul, ← hr, hk, inv_mul_cancel_left]
    exact hkF
  have hφ : IsCodeModel 2048 (mul16 ε) φ (φ 256) := by
    refine ⟨hmul, mul16_lt ε, fun p hp q hq h => ?_, fun p hp => ?_, fun w hw => ?_⟩
    ·
      have h1 := (hπ _ _).mp h
      obtain ⟨s, hs4, hs⟩ := eq_zero_of_mem_F₁ hM hΦ hF₁ h1
      have h2 : Φ (lift16 q) = Φ ((lift16 p).1, (lift16 p).2.1 ^^^ s, (lift16 p).2.2) := by
        rw [hΦ.mul_zero (s0_fix _ (lift16_snd_mem p) s hs4), hs]
        group
      have h3 := hΦ.inj (lift16 q) ((lift16 p).1, (lift16 p).2.1 ^^^ s, (lift16 p).2.2)
        (lift16_fst_lt q) (lift16_fst_lt p) h2
      obtain ⟨-, h4⟩ := fin8_eq_of_xor _ _ s (lift16_code p) (lift16_code q) hs4
        (congrArg (fun x => x.2.1) h3)
      rw [h4, RuSimCode.fin8_xor_zero] at h3
      rw [← enc16_lift16 hp, ← enc16_lift16 hq, h3]
    ·
      rw [← hmul, ← hmul, hC5 p hp]
    ·
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (F₁.subgroupOf C) w
      have hcN := hfix c hw
      obtain ⟨r, hrGL, hrA, -⟩ := hM.act c hcN
      have hfixF : ∀ t : Fin 8, t.val < 4 → linApply r t = t := fun t ht => by
        have h1 : (c : G) * Φ (0, t, 0) * (c : G)⁻¹ = Φ (0, t, 0) := by
          rw [(mem_centralizer_iff.mp c.2 _ (zero_mem_F₁ hΦ hF₁ ht)).symm]
          group
        have h2 := hrA _ (hΦ.mem_A t)
        rw [h1, hΦ.ν_eq] at h2
        exact h2.symm
      have hr1 := hfixF 1 (by decide)
      have hr2 := hfixF 2 (by decide)
      rw [RuSimCode.linApply_one] at hr1
      rw [RuSimCode.linApply_two] at hr2
      obtain ⟨d₀, hd₀, hrd⟩ := code_fix_s0 r hrGL hr1 hr2
      rw [hrd] at hrA
      obtain ⟨p₀, hp₀, hpd, hp₀c⟩ := hΦ.surj c hcN d₀ hrA
      obtain ⟨k, hkF, hk⟩ := eq_lift16_mul hΦ hF₁ hp₀ (by rw [hpd]; exact hd₀)
      refine ⟨enc16 p₀, enc16_lt hp₀, ?_⟩
      show π ⟨Φ (lift16 (enc16 p₀)), _⟩ = π c
      rw [hπ]
      show (Φ (lift16 (enc16 p₀)))⁻¹ * c ∈ F₁
      rw [← hp₀c, hk]
      simpa using hkF
  have hF₁A : F₁ ≤ gmsA L T := fun b hb => ((hF₁ b).mp hb).1
  have hF₁1 : F₁ ≠ ⊥ := by
    intro h
    have h1 : Φ (0, 1, 0) ∈ F₁ := zero_mem_F₁ hΦ hF₁ (by decide)
    rw [h, mem_bot] at h1
    have := hΦ.ν_eq 1
    rw [h1, hM.ν_one] at this
    exact absurd this (by decide)
  have hO := hS.oddCore_centralizer_quotient_eq_bot h4 hCe hCL hF₁A hF₁1
  have h0 : φ 0 = 1 := hφ.eq_one (mul16_zero ε)
  have hz2 : orderOf (φ 256) = 2 := by
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [sq, ← hmul, mul16_256, h0]
    · have := hφ.inj 256 (by norm_num) 0 (by norm_num) (by rw [h, h0])
      norm_num at this
  have hp : IsPGroup 2 (centralizer ({φ 256} : Set (C ⧸ F₁.subgroupOf C))) := by
    refine IsPGroup.of_card (n := 11) ?_
    have h1 := card_eq_countP_range φ 2048 (centralizer ({φ 256} : Set (C ⧸ F₁.subgroupOf C)))
      (fun p hp => hφ.mem_V hp) (fun w hw => hφ.surj_V hw) hφ.inj (fun _ => True)
      (fun _ => true) fun _ _ => by simp
    rw [List.countP_true, List.length_range] at h1
    rw [show (2 : ℕ) ^ 11 = 2048 by norm_num, ← h1]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by simp)
  have hiso : ∀ g, g * φ 256 * g⁻¹ ∈ centralizer ({φ 256} : Set (C ⧸ F₁.subgroupOf C)) →
      g * φ 256 * g⁻¹ = φ 256 := fun g hg =>
    isolated_of_check16 hφ rfl hchk (mem_centralizer_singleton_iff.mp hg)
  have hcomm := commute_of_isolated_of_isPGroup hO hz2 hp hiso
  intro c hc
  exact hfix ⟨c, hc⟩ (hcomm _)

theorem normalizer_le_normalizer_of_codes
    (hS : SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hM : MaskCoords L T R μ ν) (hΦ : SModel L T R μ ν ε Φ)
    (hNA : normalizer (gmsA L T : Set G) ≤ normalizer (R : Set G))
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hF₁ : ∀ b, b ∈ F₁ ↔ b ∈ gmsA L T ∧ (ν b).val < 4) :
    normalizer (F₁ : Set G) ≤ normalizer (R : Set G) := by
  intro n hn
  have hnF : ∀ b ∈ F₁, n * b * n⁻¹ ∈ F₁ := fun b hb => (mem_normalizer_iff.mp hn b).mp hb
  set b₁ := Φ (0, 1, 0)
  set b₂ := Φ (0, 2, 0)
  have hb₁ : b₁ ∈ F₁ := zero_mem_F₁ hΦ hF₁ (by decide)
  have hb₂ : b₂ ∈ F₁ := zero_mem_F₁ hΦ hF₁ (by decide)
  have hcode : ∀ b ∈ F₁, ν (n * b * n⁻¹) ≠ 0 ∨ b = 1 := fun b hb => by
    by_cases h : b = 1
    · exact Or.inr h
    · left
      intro h0
      apply h
      have h1 := hM.ν_inj _ ((hF₁ _).mp (hnF b hb)).1 h0
      calc b = n⁻¹ * (n * b * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
  set s₁ := ν (n * b₁ * n⁻¹)
  set s₂ := ν (n * b₂ * n⁻¹)
  have hb₁1 : b₁ ≠ 1 := fun h => by
    have := hΦ.ν_eq 1
    rw [show Φ (0, 1, 0) = b₁ from rfl, h, hM.ν_one] at this
    exact absurd this (by decide)
  have hb₂1 : b₂ ≠ 1 := fun h => by
    have := hΦ.ν_eq 2
    rw [show Φ (0, 2, 0) = b₂ from rfl, h, hM.ν_one] at this
    exact absurd this (by decide)
  have hs₁ : s₁ ≠ 0 := ((hcode b₁ hb₁).resolve_right hb₁1)
  have hs₂ : s₂ ≠ 0 := ((hcode b₂ hb₂).resolve_right hb₂1)
  have hs₁4 : s₁.val < 4 := ((hF₁ _).mp (hnF b₁ hb₁)).2
  have hs₂4 : s₂.val < 4 := ((hF₁ _).mp (hnF b₂ hb₂)).2
  have hs₁₂ : s₁ ≠ s₂ := by
    intro h
    have h1 := hM.eq_of_ν_eq ((hF₁ _).mp (hnF b₁ hb₁)).1 ((hF₁ _).mp (hnF b₂ hb₂)).1 h
    have h2 : b₁ = b₂ := by
      calc b₁ = n⁻¹ * (n * b₁ * n⁻¹) * n := by group
        _ = n⁻¹ * (n * b₂ * n⁻¹) * n := by rw [h1]
        _ = b₂ := by group
    have := congrArg ν h2
    rw [hΦ.ν_eq, hΦ.ν_eq] at this
    exact absurd this (by decide)
  obtain ⟨g, hgN, hgA, -⟩ :=
    hM.exists_code_eq hNC hidx (gl_of_pair hs₁4 hs₂4 hs₁ hs₂ hs₁₂)
  have hb₁₂ : Φ (0, 1 ^^^ 2, 0) = b₁ * b₂ := hΦ.mul_zero (by decide)
  have hfix : ∀ b ∈ F₁, n * b * n⁻¹ = g * b * g⁻¹ := by
    intro b hb
    obtain ⟨t, ht4, rfl⟩ := eq_zero_of_mem_F₁ hM hΦ hF₁ hb
    refine hM.eq_of_ν_eq ((hF₁ _).mp (hnF _ hb)).1 (hM.normA g hgN _ (hΦ.mem_A t)) ?_
    rw [hgA _ (hΦ.mem_A t), hΦ.ν_eq]
    rcases fin8_lt_four t ht4 with rfl | rfl | rfl | rfl
    · rw [show Φ (0, 0, 0) = 1 from hΦ.one, mul_one, mul_inv_cancel, hM.ν_one,
        RuSimCode.linApply_zero]
    · rw [RuSimCode.linApply_one]
    · rw [RuSimCode.linApply_two]
    · rw [hb₁₂, show n * (b₁ * b₂) * n⁻¹ = (n * b₁ * n⁻¹) * (n * b₂ * n⁻¹) by group,
        hM.ν_mul _ ((hF₁ _).mp (hnF b₁ hb₁)).1 _ ((hF₁ _).mp (hnF b₂ hb₂)).1,
        RuSimCode.linApply_xor, RuSimCode.linApply_one, RuSimCode.linApply_two]
  have hgn : g⁻¹ * n ∈ centralizer (F₁ : Set G) := by
    refine mem_centralizer_iff.mpr fun b hb => ?_
    have h1 := hfix b hb
    calc b * (g⁻¹ * n) = g⁻¹ * (g * b * g⁻¹) * n := by group
      _ = g⁻¹ * (n * b * n⁻¹) * n := by rw [h1]
      _ = g⁻¹ * n * b := by group
  have := centralizer_le_normalizer_of_codes hS h4 hCe hCL hM hΦ hNA hF₁ hgn
  rw [show n = g * (g⁻¹ * n) by group]
  exact mul_mem hgN this

theorem mem_four_of_card {F : Subgroup G}
    (hcard : Nat.card F = 4) {x₁ x₂ x₃ x₄ : G} (h₁ : x₁ ∈ F) (h₂ : x₂ ∈ F) (h₃ : x₃ ∈ F)
    (h₄ : x₄ ∈ F) (hd : [ν x₁, ν x₂, ν x₃, ν x₄].Nodup) :
    ∀ x ∈ F, ν x = ν x₁ ∨ ν x = ν x₂ ∨ ν x = ν x₃ ∨ ν x = ν x₄ := by
  classical
  intro x hx
  by_contra hne
  push Not at hne
  obtain ⟨n₁, n₂, n₃, n₄⟩ := hne
  have : Fintype G := Fintype.ofFinite G
  set s : Finset (Fin 8) := (Finset.univ.filter fun x : G => x ∈ F).image ν with hs
  have hsub : ({ν x₁, ν x₂, ν x₃, ν x₄, ν x} : Finset (Fin 8)) ⊆ s := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [hs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, h₁, rfl⟩
    · exact ⟨_, h₂, rfl⟩
    · exact ⟨_, h₃, rfl⟩
    · exact ⟨_, h₄, rfl⟩
    · exact ⟨_, hx, rfl⟩
  have h5 : ({ν x₁, ν x₂, ν x₃, ν x₄, ν x} : Finset (Fin 8)).card = 5 := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hd
    obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hd
    rw [Finset.card_insert_of_notMem (by simp [d12, d13, d14, Ne.symm n₁]),
      Finset.card_insert_of_notMem (by simp [d23, d24, Ne.symm n₂]),
      Finset.card_insert_of_notMem (by simp [d34, Ne.symm n₃]),
      Finset.card_insert_of_notMem (by simp [Ne.symm n₄]), Finset.card_singleton]
  have h6 : s.card ≤ 4 := by
    calc s.card ≤ (Finset.univ.filter fun x : G => x ∈ F).card := Finset.card_image_le
      _ = 4 := by rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]; exact hcard
  have := Finset.card_le_card hsub
  omega

theorem card_le_two_of_forall {F : Subgroup G} {b : G} (h : ∀ x ∈ F, x = 1 ∨ x = b) :
    Nat.card F ≤ 2 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter fun x : G => x ∈ F).card ≤ ({1, b} : Finset G).card :=
        Finset.card_le_card fun x hx => by
          rcases h x (Finset.mem_filter.mp hx).2 with rfl | rfl <;> simp
    _ ≤ 2 := Finset.card_le_two

omit [Finite G] in
theorem mem_map_conj {F : Subgroup G} {g y : G} :
    y ∈ F.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ F := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem normalizer_le_of_model
    (hS : SzR G L T R 1 y d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hM : MaskCoords L T R μ ν) (hΦ : SModel L T R μ ν ε Φ)
    (hNA : normalizer (gmsA L T : Set G) ≤ normalizer (R : Set G))
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {F : Subgroup G} (hFA : F ≤ gmsA L T)
    (hc : Nat.card F = 4) : normalizer (F : Set G) ≤ normalizer (R : Set G) := by
  classical
  obtain ⟨b₁, hb₁, hb₁1⟩ : ∃ b₁ ∈ F, b₁ ≠ 1 := by
    by_contra h
    push Not at h
    have := card_le_two_of_forall (F := F) (b := 1) fun x hx => Or.inl (h x hx)
    omega
  obtain ⟨b₂, hb₂, hb₂1, hb₂₁⟩ : ∃ b₂ ∈ F, b₂ ≠ 1 ∧ b₂ ≠ b₁ := by
    by_contra h
    push Not at h
    have := card_le_two_of_forall (F := F) (b := b₁) fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    omega
  have hν₁ : ν b₁ ≠ 0 := fun h => hb₁1 (hM.ν_inj _ (hFA hb₁) h)
  have hν₂ : ν b₂ ≠ 0 := fun h => hb₂1 (hM.ν_inj _ (hFA hb₂) h)
  have hν₁₂ : ν b₁ ≠ ν b₂ := fun h => hb₂₁ (hM.eq_of_ν_eq (hFA hb₂) (hFA hb₁) h.symm)
  have hFall := mem_four_of_card (ν := ν) hc (one_mem F) hb₁ hb₂ (mul_mem hb₁ hb₂) (by
    rw [hM.ν_one, hM.ν_mul _ (hFA hb₁) _ (hFA hb₂)]
    exact nodup_four _ _ hν₁ hν₂ hν₁₂)
  rw [hM.ν_one, hM.ν_mul _ (hFA hb₁) _ (hFA hb₂)] at hFall
  obtain ⟨r, hr, hr1, hr2⟩ := gl_to_pair _ _ hν₁ hν₂ hν₁₂
  obtain ⟨g, hgN, hgA, -⟩ := hM.exists_code_eq hNC hidx hr
  set F' := F.map (MulAut.conj g).toMonoidHom with hF'
  have hF'c : ∀ b, b ∈ F' ↔ b ∈ gmsA L T ∧ (ν b).val < 4 := by
    intro b
    rw [mem_map_conj]
    constructor
    · intro hb
      have hbA : b ∈ gmsA L T := by
        have := hM.normA g hgN _ (hFA hb)
        rwa [show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at this
      refine ⟨hbA, ?_⟩
      have h1 := hgA _ (hFA hb)
      rw [show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at h1
      rw [h1]
      exact lt_four_of_pair r _ _ hr1 hr2 _ (hFall _ hb)
    · rintro ⟨hbA, hb4⟩
      have hx : ∃ x ∈ F, linApply r (ν x) = ν b := by
        rcases fin8_lt_four _ hb4 with h | h | h | h
        · exact ⟨1, one_mem F, by rw [hM.ν_one, RuSimCode.linApply_zero, h]⟩
        · exact ⟨b₁, hb₁, by rw [hr1, h]⟩
        · exact ⟨b₂, hb₂, by rw [hr2, h]⟩
        · exact ⟨b₁ * b₂, mul_mem hb₁ hb₂, by
            rw [hM.ν_mul _ (hFA hb₁) _ (hFA hb₂), RuSimCode.linApply_xor, hr1, hr2, h]⟩
      obtain ⟨x, hxF, hxb⟩ := hx
      have h1 : g * x * g⁻¹ = b :=
        hM.eq_of_ν_eq (hM.normA g hgN _ (hFA hxF)) hbA (by rw [hgA _ (hFA hxF), hxb])
      rw [← h1, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hxF
  have hN' := normalizer_le_normalizer_of_codes hS h4 hCe hCL hM hΦ hNA hNC hidx hF'c
  intro n hn
  have hgn : g * n * g⁻¹ ∈ normalizer (F' : Set G) := by
    refine mem_normalizer_iff.mpr fun y => ?_
    rw [mem_map_conj, mem_map_conj,
      show g⁻¹ * (g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹) * g = n * (g⁻¹ * y * g) * n⁻¹ by group]
    exact mem_normalizer_iff.mp hn _
  have := hN' hgn
  rw [show n = g⁻¹ * (g * n * g⁻¹) * g by group]
  exact mul_mem (mul_mem (inv_mem hgN) this) hgN

theorem normalizer_le_of_le_gmsA_of_card_eq_four
    {R₂ : Subgroup G}
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) {F₁ : Subgroup G} (hF₁ : F₁ ≤ gmsA L T)
    (hc : Nat.card F₁ = 4) : normalizer (F₁ : Set G) ≤ normalizer (R : Set G) := by
  obtain ⟨μ, ν, hM⟩ := hS.exists_maskCoords h34 hR₂ h4 hNS
  have hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R := by
    rw [hS.centralizer_gmsA_eq h34 hR₂ h4 hCV hCe hCL]
    exact inf_eq_right.mpr le_normalizer
  have hidx := hS.relIndex_normalizer_eq h34 hR₂ h4 hCV hNS
  have hNA := (hS.normalizer_gmsA_eq h34 hR₂ h4 hCV hCe hCL hNS).le
  obtain ⟨ε, Φ, hΦ⟩ := hM.exists_sModel hNC hidx
  exact normalizer_le_of_model hS h4 hCe hCL hM hΦ hNA hNC hidx hF₁ hc

end Main

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
