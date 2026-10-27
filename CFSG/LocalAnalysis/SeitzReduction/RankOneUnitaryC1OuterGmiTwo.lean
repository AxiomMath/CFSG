module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiOne
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiCatHolds
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups

namespace GmiLayerHyp

variable {X : Type} [Group X] [Finite X] {f : ℕ} {Q : Sylow 2 X} {J F A₁ K₀ Dv : Subgroup X}
  {v e : X} {τ : MulAut X} (h : GmiLayerHyp X f Q J F A₁ K₀ Dv v e τ)
include h

theorem inf_eq_bot_of_ne {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁)
    (h₂ : CFSG.IsComponent K₂) (hne : K₂ ≠ K₁) (hZ : Subgroup.center K₁ = ⊥) :
    K₁ ⊓ K₂ = ⊥ := by
  rw [eq_bot_iff, ← h.inf_centralizer_eq_bot hZ]
  exact inf_le_inf_left _ (h.le_centralizer_of_ne h₁ h₂ hne)

theorem mem_sup_dec {K₁ K₂ : Subgroup X} (h₂ : CFSG.IsComponent K₂) {x : X}
    (hx : x ∈ K₁ ⊔ K₂) : ∃ x₁ ∈ K₁, ∃ x₂ ∈ K₂, x₁ * x₂ = x :=
  ncyc_exists_mul_of_mem_sup (fun y _ => gmi_top_le_normalizer (h.component_normal h₂) (mem_top y))
    hx

theorem layer_eq_sup {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂)
    (hall : ∀ K : Subgroup X, CFSG.IsComponent K → K = K₁ ∨ K = K₂) :
    CFSG.layer X = K₁ ⊔ K₂ := by
  refine le_antisymm (sSup_le fun K hK => ?_) (sup_le (CFSG.LocalCores.component_le_layer h₁)
    (CFSG.LocalCores.component_le_layer h₂))
  rcases hall K hK with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem layer_inf_centralizer_le {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁)
    (h₂ : CFSG.IsComponent K₂) (hne : K₂ ≠ K₁) (hZ : Subgroup.center K₁ = ⊥)
    (hE : CFSG.layer X = K₁ ⊔ K₂) : CFSG.layer X ⊓ centralizer (K₁ : Set X) ≤ K₂ := by
  intro c hc
  obtain ⟨hcE, hcC⟩ := mem_inf.mp hc
  rw [hE] at hcE
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h.mem_sup_dec h₂ hcE
  have hx₂C := h.le_centralizer_of_ne h₁ h₂ hne hx₂
  have hx₁C : x₁ ∈ centralizer (K₁ : Set X) := by
    rw [show x₁ = x₁ * x₂ * x₂⁻¹ by group]
    exact mul_mem hcC (inv_mem hx₂C)
  have hx₁1 : x₁ = 1 := by
    have : x₁ ∈ K₁ ⊓ centralizer (K₁ : Set X) := mem_inf.mpr ⟨hx₁, hx₁C⟩
    rw [h.inf_centralizer_eq_bot hZ] at this
    exact Subgroup.mem_bot.mp this
  rw [hx₁1, one_mul]
  exact hx₂

theorem exists_mul_of_mem_Q_layer {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁)
    (h₂ : CFSG.IsComponent K₂) (hne : K₂ ≠ K₁) (hZ : Subgroup.center K₁ = ⊥)
    (hE : CFSG.layer X = K₁ ⊔ K₂) {x : X} (hxQ : x ∈ (Q : Subgroup X))
    (hxE : x ∈ CFSG.layer X) :
    ∃ x₁ ∈ (Q : Subgroup X) ⊓ K₁, ∃ x₂ ∈ (Q : Subgroup X) ⊓ K₂, x₁ * x₂ = x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_Q h₁ hxQ
  have hbE : b ∈ CFSG.layer X := by
    rw [show b = a⁻¹ * (a * b) by group]
    exact mul_mem (inv_mem (CFSG.LocalCores.component_le_layer h₁ (mem_inf.mp ha).2)) hxE
  have hbK₂ := h.layer_inf_centralizer_le h₁ h₂ hne hZ hE (mem_inf.mpr ⟨hbE, (mem_inf.mp hb).2⟩)
  exact ⟨a, ha, b, mem_inf.mpr ⟨(mem_inf.mp hb).1, hbK₂⟩, rfl⟩

theorem card_sup_inf {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁)
    (h₂ : CFSG.IsComponent K₂) (hne : K₂ ≠ K₁) (hZ : Subgroup.center K₁ = ⊥) :
    Nat.card ((Q : Subgroup X) ⊓ K₁ ⊔ (Q : Subgroup X) ⊓ K₂ : Subgroup X) =
      Nat.card ((Q : Subgroup X) ⊓ K₁ : Subgroup X) * Nat.card ((Q : Subgroup X) ⊓ K₂ : Subgroup X) := by
  have hc := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := (Q : Subgroup X) ⊓ K₁) (B := (Q : Subgroup X) ⊓ K₂) (fun b hb =>
      gmi_mem_normalizer_inf (mem_inf.mp hb).1
        (gmi_top_le_normalizer (h.component_normal h₁) (mem_top b)))
  have hbot : (Q : Subgroup X) ⊓ K₁ ⊓ ((Q : Subgroup X) ⊓ K₂) = ⊥ := by
    rw [eq_bot_iff, ← h.inf_eq_bot_of_ne h₁ h₂ hne hZ]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rwa [hbot, Subgroup.card_bot, mul_one] at hc

theorem two_mul_card_le (hcen : ∀ K : Subgroup X, CFSG.IsComponent K → Subgroup.center K = ⊥)
    {Y : Subgroup X} (hYQ : Y ≤ (Q : Subgroup X)) (hYE : Y ≤ CFSG.layer X) :
    2 * Nat.card Y ≤ Nat.card (Q : Subgroup X) := by
  have hvY : v ∉ Y := fun hv => h.v_not_mem_layer hcen (hYE hv)
  have hvN : v ∈ normalizer (Y : Set X) := mem_normalizer_iff.mpr fun y => by
    rw [h.v_comm y, mul_inv_cancel_right]
  have hvv : v * v = 1 := by rw [← sq]; exact h.v_sq
  have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two hvY hvN hvv
  have h3 := relIndex_mul_card (H := Y) (K := Y ⊔ zpowers v)
  rw [h2, inf_of_le_left le_sup_left] at h3
  have hle : Y ⊔ zpowers v ≤ (Q : Subgroup X) :=
    sup_le hYQ (zpowers_le.mpr (h.J_le_Q h.v_mem))
  rw [h3]
  exact Subgroup.card_le_of_le hle

theorem two_type (hC4 : GmiCatFourInput) (hCS : GmiCatSimpleInput)
    (hSchur : GmiCatSchurInput) {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁)
    (h₂ : CFSG.IsComponent K₂) (hne : K₂ ≠ K₁) :
    (∀ x ∈ (Q : Subgroup X) ⊓ K₁, x ^ 2 = 1) ∧
    ((Nonempty (K₁ ≃* PSL(2, GaloisField 2 f)) ∧ Nat.card K₁ = Nat.card K₀ ∧
        Nat.card ((Q : Subgroup X) ⊓ K₁ : Subgroup X) = 2 ^ f) ∨
      (f = 2 ∧ (∃ (p n : ℕ) (_ : Fact p.Prime), Odd p ∧ 0 < n ∧
          (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧ Nonempty (K₁ ≃* PSL(2, GaloisField p n))) ∧
        Nat.card ((Q : Subgroup X) ⊓ K₁ : Subgroup X) = 4) ∨
      (f = 2 ∧ Nonempty (K₁ ≃* goldschmidtJ1) ∧
        Nat.card ((Q : Subgroup X) ⊓ K₁ : Subgroup X) = 8)) := by
  have hcen := fun K (hK : CFSG.IsComponent K) => h.center_eq_bot hC4 hSchur hK
  set T₁ := (Q : Subgroup X) ⊓ K₁ with hT₁
  set T₂ := (Q : Subgroup X) ⊓ K₂ with hT₂
  have hT₁S := h.isSylowOf_inf h₁
  have hW₁ := h.card_omega_inf_ge hC4 h₁ (hcen K₁ h₁)
  have hW₂ := h.card_omega_inf_ge hC4 h₂ (hcen K₂ h₂)
  have hWW : Nat.card (gmiOmega Q ⊓ K₁ : Subgroup X) *
      Nat.card (gmiOmega Q ⊓ K₂ : Subgroup X) ≤ 2 * (2 ^ f) ^ 2 := by
    have hbot : (gmiOmega Q ⊓ K₁) ⊓ (gmiOmega Q ⊓ K₂) = ⊥ := by
      rw [eq_bot_iff, ← h.inf_eq_bot_of_ne h₁ h₂ hne (hcen K₁ h₁)]
      exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    rw [← h.card_sup_of_le_omega inf_le_left inf_le_left hbot]
    exact h.card_le_of_le_omega hcen (sup_le inf_le_left inf_le_left)
  have hW₁le : Nat.card (gmiOmega Q ⊓ K₁ : Subgroup X) ≤ 2 * 2 ^ f := by
    have hmul : Nat.card (gmiOmega Q ⊓ K₁ : Subgroup X) * 2 ^ f ≤ (2 * 2 ^ f) * 2 ^ f :=
      calc _ ≤ Nat.card (gmiOmega Q ⊓ K₁ : Subgroup X) *
            Nat.card (gmiOmega Q ⊓ K₂ : Subgroup X) := Nat.mul_le_mul_left _ hW₂
        _ ≤ 2 * (2 ^ f) ^ 2 := hWW
        _ = (2 * 2 ^ f) * 2 ^ f := by ring
    exact Nat.le_of_mul_le_mul_right hmul (by positivity)
  have hWT : gmiOmega Q ⊓ K₁ ≤ T₁ := le_inf (inf_le_left.trans h.omega_le_Q) inf_le_right
  have hq4 := h.four_le
  have hf2_of : 2 ^ f ≤ 8 → f = 2 := by
    intro h8
    obtain ⟨k, hk⟩ := h.even
    have hf3 : f ≤ 3 := by
      by_contra hf
      push Not at hf
      have : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    have := h.two_le
    omega
  rcases h.simple_type hC4 h₁ (hcen K₁ h₁) with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ |
      ⟨p, n, hp, hpodd, hn0, h8, ⟨e'⟩⟩ | ⟨e'⟩
  ·
    obtain ⟨hKcard, hTcard, hTsq⟩ := (hCS X K₁ T₁ hT₁S).1 n (by omega) ⟨e'⟩
    have hTW : T₁ ≤ gmiOmega Q ⊓ K₁ := le_inf (h.le_omega_of_sq h₁ le_rfl hTsq) inf_le_right
    have hTeq : Nat.card T₁ = Nat.card (gmiOmega Q ⊓ K₁ : Subgroup X) :=
      le_antisymm (Subgroup.card_le_of_le hTW) (Subgroup.card_le_of_le hWT)
    rw [← hTeq, hTcard] at hW₁ hW₁le
    have hlo : f ≤ n := (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).mp hW₁
    have hhi : n ≤ f + 1 := (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).mp
      (by rw [pow_succ]; linarith)
    have hnf : n = f := by
      rcases (show n = f ∨ n = f + 1 by omega) with h1 | h1
      · exact h1
      · exfalso
        have hdvd := h.card_K₀_dvd hC4 h₁
        have e₀ : ↥K₁ ≃* (↥K₁ ⧸ Subgroup.center K₁) :=
          ((QuotientGroup.quotientMulEquivOfEq (hcen K₁ h₁)).trans QuotientGroup.quotientBot).symm
        rw [← Nat.card_congr e₀.toEquiv, h.card_K₀, hKcard, h1,
          show (2 ^ (f + 1)) ^ 2 = 4 * ((2 ^ f) ^ 2) ^ 1 by ring] at hdvd
        exact gmi_not_dvd h.two_le hdvd
    subst hnf
    exact ⟨hTsq, Or.inl ⟨⟨e'⟩, by rw [hKcard, h.card_K₀], hTcard⟩⟩
  ·
    exfalso
    obtain ⟨hTcard, hW⟩ := (hCS X K₁ T₁ hT₁S).2.2.1 n hn ⟨e'⟩
    have hWn := hW _ hWT (fun x hx => h.omega_sq (mem_inf.mp hx).1)
    have hT₂ : 2 ^ f ≤ Nat.card T₂ := hW₂.trans
      (Subgroup.card_le_of_le (le_inf (inf_le_left.trans h.omega_le_Q) inf_le_right))
    have h2 := h.two_mul_card_le hcen (sup_le inf_le_left inf_le_left : T₁ ⊔ T₂ ≤ Q)
      (sup_le (inf_le_right.trans (CFSG.LocalCores.component_le_layer h₁))
        (inf_le_right.trans (CFSG.LocalCores.component_le_layer h₂)))
    rw [h.card_sup_inf h₁ h₂ hne (hcen K₁ h₁), hTcard] at h2
    have hL6 := h.L6
    have hqn : 2 ^ f ≤ 2 ^ n := hW₁.trans hWn
    have hq3 : (2 ^ f) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hqn 3
    have hfq : f < 2 ^ f := Nat.lt_two_pow_self
    set q := 2 ^ f with hq
    have h4 : 2 * q ^ 4 ≤ 8 * f * q ^ 2 := by nlinarith
    have hq2 : 0 < q ^ 2 := by positivity
    have h5 : q ^ 2 * (2 * q ^ 2) ≤ q ^ 2 * (8 * f) := by nlinarith
    have h6 := Nat.le_of_mul_le_mul_left h5 hq2
    nlinarith
  ·
    obtain ⟨hTcard, hTsq⟩ := (hCS X K₁ T₁ hT₁S).2.2.2.1 p n hpodd hn0 h8 ⟨e'⟩
    have hW₁T : Nat.card (gmiOmega Q ⊓ K₁ : Subgroup X) ≤ 4 :=
      hTcard ▸ Subgroup.card_le_of_le hWT
    exact ⟨hTsq, Or.inr (Or.inl ⟨hf2_of (by omega), ⟨p, n, hp, hpodd, hn0, h8, ⟨e'⟩⟩, hTcard⟩)⟩
  ·
    obtain ⟨hKcard, hTsq⟩ := (hCS X K₁ T₁ hT₁S).2.2.2.2 e'
    have hTcard : Nat.card T₁ = 8 := by
      rw [hT₁S.card_eq, hKcard, show (175560 : ℕ) = 2 ^ 3 * 21945 by norm_num,
        CFSG.Monster.B.Recog.GoldschmidtArith.factorization_two_pow_mul_odd 3 ⟨10972, by norm_num⟩]
      norm_num
    have hW₁T : Nat.card (gmiOmega Q ⊓ K₁ : Subgroup X) ≤ 8 :=
      hTcard ▸ Subgroup.card_le_of_le hWT
    exact ⟨hTsq, Or.inr (Or.inr ⟨hf2_of (by omega), e', hTcard⟩)⟩

theorem fix_part {K : Subgroup X} (hZ : Subgroup.center K = ⊥) (hτK : ∀ x ∈ K, τ x ∈ K)
    {a k c : X} (ha : a ∈ A₁) (hk : k ∈ K) (hc : c ∈ centralizer (K : Set X))
    (hkc : k * c = a) : τ k = k := by
  have hτc : τ c ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := mem_centralizer_iff.mp hc (τ y) (hτK y hy)
    have e := congrArg τ h1
    rw [map_mul, map_mul, h.τ_inv] at e
    exact e
  have hτa : τ a = a := h.τ_K₀ a (h.A₁_le_K₀ ha)
  have e1 : τ k * τ c = k * c := by rw [← map_mul, hkc, hτa]
  have hmem : k⁻¹ * τ k ∈ K ⊓ centralizer (K : Set X) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hk) (hτK _ hk), ?_⟩
    rw [show k⁻¹ * τ k = c * (τ c)⁻¹ by
      calc k⁻¹ * τ k = k⁻¹ * (τ k * τ c) * (τ c)⁻¹ := by group
        _ = k⁻¹ * (k * c) * (τ c)⁻¹ := by rw [e1]
        _ = c * (τ c)⁻¹ := by group]
    exact mul_mem hc (inv_mem hτc)
  rw [h.inf_centralizer_eq_bot hZ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

theorem fix_of_card_eq (hC4 : GmiCatFourInput) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hZ : Subgroup.center K = ⊥) (hτK : ∀ x ∈ K, τ x ∈ K)
    (hcard : Nat.card ((Q : Subgroup X) ⊓ K : Subgroup X) = 2 ^ f) :
    ∀ x ∈ (Q : Subgroup X) ⊓ K, τ x = x := by
  have hdec : ∀ a : A₁, ∃ k ∈ (Q : Subgroup X) ⊓ K,
      ∃ c ∈ (Q : Subgroup X) ⊓ centralizer (K : Set X), k * c = a :=
    fun a => h.exists_mul_of_mem_Q hK (h.J_le_Q (h.F_le (h.A₁_le_F a.2)))
  choose k hk c hc hkc using hdec
  let φ : A₁ → ((Q : Subgroup X) ⊓ K : Subgroup X) := fun a => ⟨k a, hk a⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have hkab : k a = k b := congrArg Subtype.val hab
    have hmem : (a : X)⁻¹ * b ∈ K₀ ⊓ centralizer (K : Set X) := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (h.A₁_le_K₀ a.2)) (h.A₁_le_K₀ b.2), ?_⟩
      rw [← hkc a, ← hkc b, hkab, show (k b * c a)⁻¹ * (k b * c b) = (c a)⁻¹ * c b by group]
      exact mul_mem (inv_mem (mem_inf.mp (hc a)).2) (mem_inf.mp (hc b)).2
    rw [h.K₀_inf_centralizer hC4 hK, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem
  have hbij := hφ.bijective_of_nat_card_le (by rw [hcard, h.card_A₁])
  intro x hx
  obtain ⟨a, ha⟩ := hbij.2 ⟨x, hx⟩
  have hxa : k a = x := congrArg Subtype.val ha
  rw [← hxa]
  exact h.fix_part hZ hτK a.2 (mem_inf.mp (hk a)).2 (mem_inf.mp (hc a)).2 (hkc a)

theorem fix_T_of_fix
    (hC4 : GmiCatFourInput) (hCS : GmiCatSimpleInput) (hSchur : GmiCatSchurInput)
    {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂) (hne : K₂ ≠ K₁)
    (hfix : K₁.map τ.toMonoidHom = K₁) : ∀ x ∈ (Q : Subgroup X) ⊓ K₁, τ x = x := by
  have hZ₁ := h.center_eq_bot hC4 hSchur h₁
  have hτK : ∀ x ∈ K₁, τ x ∈ K₁ := fun x hx => hfix ▸ Subgroup.mem_map_of_mem _ hx
  have hτT : ∀ y ∈ (Q : Subgroup X) ⊓ K₁, τ y ∈ (Q : Subgroup X) ⊓ K₁ := fun y hy =>
    mem_inf.mpr ⟨h.τ_Q _ (mem_inf.mp hy).1, hτK _ (mem_inf.mp hy).2⟩
  obtain ⟨-, hty⟩ := h.two_type hC4 hCS hSchur h₁ h₂ hne
  rcases hty with ⟨-, -, hcard⟩ | ⟨hf2, -, hcard⟩ | ⟨-, ⟨eJ⟩, -⟩
  · exact h.fix_of_card_eq hC4 h₁ hZ₁ hτK hcard
  · exact h.fix_of_card_eq hC4 h₁ hZ₁ hτK (by rw [hcard, hf2]; norm_num)
  · exact gmi_fix_sylow_of_j1 eJ (h.isSylowOf_inf h₁) τ hτK h.τ_inv hτT

end GmiLayerHyp

end CFSG.SeitzReduction.RankOne
