module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiCount

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups

theorem gmi_not_dvd {f k n : ℕ} (hf : 2 ≤ f) :
    ¬ 2 ^ f * ((2 ^ f) ^ 2 - 1) ∣ 2 ^ n * (4 * ((2 ^ f) ^ 2) ^ k - 1) := by
  intro hdvd
  set a := (2 ^ f) ^ 2 - 1 with ha
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq16 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
  have ha15 : 15 ≤ a := by omega
  have haodd : Odd a := by
    rw [ha, ← pow_mul]
    exact CFSG.Monster.B.Recog.GoldschmidtArith.odd_two_pow_sub_one (by omega)
  have h1 : a ∣ 2 ^ n * (4 * ((2 ^ f) ^ 2) ^ k - 1) := (Dvd.intro_left _ rfl).trans hdvd
  have hcop : Nat.Coprime a (2 ^ n) := Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr haodd)
  have h2 : a ∣ 4 * ((2 ^ f) ^ 2) ^ k - 1 := hcop.dvd_of_dvd_mul_left h1
  have h3 : a ∣ ((2 ^ f) ^ 2) ^ k - 1 := by
    have := Nat.sub_dvd_pow_sub_pow ((2 ^ f) ^ 2) 1 k
    rwa [one_pow] at this
  have h4 : a ∣ 4 * (((2 ^ f) ^ 2) ^ k - 1) := Dvd.dvd.mul_left h3 4
  have hpos : 1 ≤ ((2 ^ f) ^ 2) ^ k := Nat.one_le_pow _ _ (by positivity)
  have h5 : 4 * ((2 ^ f) ^ 2) ^ k - 1 - 4 * (((2 ^ f) ^ 2) ^ k - 1) = 3 := by omega
  have h6 : a ∣ 3 := by rw [← h5]; exact Nat.dvd_sub h2 h4
  have := Nat.le_of_dvd (by norm_num) h6
  omega

namespace GmiLayerHyp

variable {X : Type} [Group X] [Finite X] {f : ℕ} {Q : Sylow 2 X} {J F A₁ K₀ Dv : Subgroup X}
  {v e : X} {τ : MulAut X} (h : GmiLayerHyp X f Q J F A₁ K₀ Dv v e τ)
include h

theorem simple_type (hC4 : GmiCatFourInput) {K : Subgroup X}
    (hK : CFSG.IsComponent K) (hZ : Subgroup.center K = ⊥) :
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ≃* PSL(2, GaloisField 2 n))) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* PSU3 2 n)) ∨
    (∃ (p n : ℕ) (_ : Fact p.Prime), Odd p ∧ 0 < n ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧
      Nonempty (K ≃* PSL(2, GaloisField p n))) ∨
    Nonempty (K ≃* goldschmidtJ1) := by
  have e₀ : ↥K ≃* (↥K ⧸ Subgroup.center K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  rcases h.type K ((CFSG.isComponent_iff_open K).mp hK) with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ |
      ⟨n, hn, ⟨e'⟩⟩ | ⟨p, n, hp, hpodd, hn0, -, h8, ⟨e'⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e₀.trans e'⟩⟩
  · exact ((h.not_sz hC4 hK n).false e').elim
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e₀.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, n, hp, hpodd, hn0, h8, ⟨e₀.trans e'⟩⟩))
  · exact (h.not_ree hC4 hK m hcard).elim
  · exact Or.inr (Or.inr (Or.inr ⟨e₀.trans e'⟩))

theorem le_omega_of_sq {K T : Subgroup X} (hK : CFSG.IsComponent K)
    (hT : T ≤ (Q : Subgroup X) ⊓ K) (hT2 : ∀ x ∈ T, x ^ 2 = 1) : T ≤ gmiOmega Q := fun x hx =>
  h.mem_omega (mem_inf.mp (hT hx)).1
    (CFSG.LocalCores.component_le_layer hK (mem_inf.mp (hT hx)).2) (hT2 x hx)

theorem F_le_Q : F ≤ (Q : Subgroup X) := h.F_le.trans h.J_le_Q

theorem four_le : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le

theorem case_one (hC4 : GmiCatFourInput) (hCS : GmiCatSimpleInput)
    (hSchur : GmiCatSchurInput) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hE : CFSG.layer X = K) :
    ∃ (p n : ℕ) (_ : Fact p.Prime), (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
      Nonempty (K ≃* PSL(2, GaloisField p n)) ∧ IsSylowOf 2 F K ∧ Dv ≤ K := by
  have hcen := fun K' (hK' : CFSG.IsComponent K') => h.center_eq_bot hC4 hSchur hK'
  have hZ := hcen K hK
  set T := (Q : Subgroup X) ⊓ K with hT
  have hTS := h.isSylowOf_inf hK
  have hFK : F ≤ K := hE ▸ h.F_le_layer
  have hFT : F ≤ T := le_inf h.F_le_Q hFK
  have hDK : Dv ≤ K := hE ▸ (h.D_le.trans h.K₀_le_layer)
  have hK₀K : K₀ ≤ K := hE ▸ h.K₀_le_layer
  have hFcardT : (2 ^ f) ^ 2 ∣ Nat.card T := h.card_F ▸ Subgroup.card_dvd_of_le hFT
  have hq4 := h.four_le
  have hq16 : 16 ∣ (2 ^ f) ^ 2 := by
    have h2f : 2 ^ 4 ∣ (2 ^ f) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by have := h.two_le; omega)
    simpa using h2f
  rcases h.simple_type hC4 hK hZ with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ |
      ⟨p, n, hp, hpodd, hn0, h8, ⟨e'⟩⟩ | ⟨e'⟩
  ·
    obtain ⟨hKcard, hTcard, hTsq⟩ := (hCS X K T hTS).1 n (by omega) ⟨e'⟩
    have hTle := h.card_le_of_le_omega hcen (h.le_omega_of_sq hK le_rfl hTsq)
    rw [hTcard] at hTle hFcardT
    have hlo : 2 * f ≤ n := by
      rw [← pow_mul] at hFcardT
      have := (Nat.pow_dvd_pow_iff_le_right (show 1 < 2 by norm_num)).mp hFcardT
      omega
    have hhi : n ≤ 2 * f + 1 := by
      have : 2 ^ n ≤ 2 ^ (2 * f + 1) := by
        rw [show 2 ^ (2 * f + 1) = 2 * (2 ^ f) ^ 2 by ring]
        exact hTle
      exact (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).mp this
    have hn2f : n = 2 * f := by
      rcases (show n = 2 * f ∨ n = 2 * f + 1 by omega) with h1 | h1
      · exact h1
      · exfalso
        have hdvd : Nat.card K₀ ∣ Nat.card K := Subgroup.card_dvd_of_le hK₀K
        rw [h.card_K₀, hKcard, h1, show (2 ^ (2 * f + 1)) ^ 2 = 4 * ((2 ^ f) ^ 2) ^ 2 by ring]
          at hdvd
        exact gmi_not_dvd h.two_le hdvd
    subst hn2f
    have hFeq : F = T := Subgroup.eq_of_le_of_card_ge hFT (by rw [hTcard, h.card_F, ← pow_mul,
      mul_comm])
    refine ⟨2, 2 * f, ⟨Nat.prime_two⟩, Or.inl ⟨rfl, by omega⟩, ⟨e'⟩, ?_, hDK⟩
    rw [hFeq]
    exact hTS
  ·
    exfalso
    obtain ⟨hTcard, hW⟩ := (hCS X K T hTS).2.2.1 n hn ⟨e'⟩
    have hFW := hW F hFT h.F_sq
    rw [h.card_F] at hFW
    have hTQ : Nat.card T ≤ Nat.card (Q : Subgroup X) := Subgroup.card_le_of_le inf_le_left
    rw [hTcard] at hTQ
    have hL6 := h.L6
    have h3 : ((2 ^ f) ^ 2) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hFW 3
    have hfq : f < 2 ^ f := Nat.lt_two_pow_self
    set q := 2 ^ f with hq
    have hq2 : 0 < q ^ 2 := by positivity
    have h4 : q ^ 2 * q ^ 4 ≤ q ^ 2 * (8 * f) := by nlinarith
    have h5 := Nat.le_of_mul_le_mul_left h4 hq2
    nlinarith
  ·
    exfalso
    obtain ⟨hTcard, -⟩ := (hCS X K T hTS).2.2.2.1 p n hpodd hn0 h8 ⟨e'⟩
    rw [hTcard] at hFcardT
    have := Nat.le_of_dvd (by norm_num) hFcardT
    nlinarith
  ·
    exfalso
    obtain ⟨hKcard, -⟩ := (hCS X K T hTS).2.2.2.2 e'
    have hdvd : (2 ^ f) ^ 2 ∣ 175560 := hKcard ▸ hFcardT.trans (Subgroup.card_dvd_of_le hTS.le)
    exact absurd (hq16.trans hdvd) (by norm_num)

end GmiLayerHyp

end CFSG.SeitzReduction.RankOne
