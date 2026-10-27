module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups

namespace GmiLayerHyp

variable {X : Type} [Group X] [Finite X] {f : ℕ} {Q : Sylow 2 X} {J F A₁ K₀ Dv : Subgroup X}
  {v e : X} {τ : MulAut X} (h : GmiLayerHyp X f Q J F A₁ K₀ Dv v e τ)
include h

theorem case_two
    (hC4 : GmiCatFourInput) (hCS : GmiCatSimpleInput) (hSchur : GmiCatSchurInput)
    {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂)
    (hne : K₂ ≠ K₁) (hall : ∀ K : Subgroup X, CFSG.IsComponent K → K = K₁ ∨ K = K₂) :
    ∃ (K E₁ : Subgroup X) (p n : ℕ) (_ : Fact p.Prime),
      (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
      Nonempty (K ≃* PSL(2, GaloisField p n)) ∧
      (∀ a ∈ K, ∀ b ∈ K, a * τ b = τ b * a) ∧
      IsSylowOf 2 (F ⊓ K) K ∧
      (∀ x ∈ F, ∃ x₁ ∈ F ⊓ K, ∃ x₂ ∈ F ⊓ K, x = x₁ * τ x₂) ∧
      E₁ ≤ K ∧ E₁ ≤ normalizer ((F ⊓ K : Subgroup X) : Set X) ∧ Odd (Nat.card E₁) ∧
      ∀ d ∈ Dv, ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₁, d = e₁ * τ e₂ := by
  have hcen := fun K (hK : CFSG.IsComponent K) => h.center_eq_bot hC4 hSchur hK
  have hZ₁ := hcen K₁ h₁
  have hE := h.layer_eq_sup h₁ h₂ hall
  set T₁ := (Q : Subgroup X) ⊓ K₁ with hT₁
  set T₂ := (Q : Subgroup X) ⊓ K₂ with hT₂
  obtain ⟨hT₁sq, hty₁⟩ := h.two_type hC4 hCS hSchur h₁ h₂ hne
  obtain ⟨hT₂sq, -⟩ := h.two_type hC4 hCS hSchur h₂ h₁ hne.symm
  have hK₁₂ : K₁ ⊓ K₂ = ⊥ := h.inf_eq_bot_of_ne h₁ h₂ hne hZ₁
  have hc21 := h.le_centralizer_of_ne h₁ h₂ hne
  have hFdec : ∀ x ∈ F, ∃ x₁ ∈ T₁, ∃ x₂ ∈ T₂, x₁ * x₂ = x := fun x hx =>
    h.exists_mul_of_mem_Q_layer h₁ h₂ hne hZ₁ hE (h.F_le_Q hx) (h.F_le_layer hx)
  have hFT : F ≤ T₁ ⊔ T₂ := fun x hx => by
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hFdec x hx
    exact mul_mem (mem_sup_left hx₁) (mem_sup_right hx₂)
  have hτ₁ := hall _ (CFSG.LocalCores.isComponent_map_mulEquiv τ h₁)
  have hτ₂ := hall _ (CFSG.LocalCores.isComponent_map_mulEquiv τ h₂)
  have hinj : ∀ {A B : Subgroup X}, A.map τ.toMonoidHom = B.map τ.toMonoidHom → A = B :=
    fun heq => Subgroup.map_injective τ.injective heq
  have hτ12 : K₁.map τ.toMonoidHom = K₂ := by
    refine hτ₁.resolve_left fun hfix => ?_
    have hfix₂ : K₂.map τ.toMonoidHom = K₂ := by
      rcases hτ₂ with h2 | h2
      · exact absurd (hinj (h2.trans hfix.symm)) hne
      · exact h2
    have hf₁ := h.fix_T_of_fix hC4 hCS hSchur h₁ h₂ hne hfix
    have hf₂ := h.fix_T_of_fix hC4 hCS hSchur h₂ h₁ hne.symm hfix₂
    obtain ⟨x, hx, hτx⟩ := h.τ_move
    apply hτx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hFdec x hx
    rw [map_mul, hf₁ x₁ hx₁, hf₂ x₂ hx₂]
  have hτ21 : K₂.map τ.toMonoidHom = K₁ := by
    rcases hτ₂ with h2 | h2
    · exact h2
    · exact absurd (hinj (hτ12.trans h2.symm)).symm hne
  have hτK12 : ∀ x ∈ K₁, τ x ∈ K₂ := fun x hx => hτ12 ▸ Subgroup.mem_map_of_mem _ hx
  have hτK21 : ∀ x ∈ K₂, τ x ∈ K₁ := fun x hx => hτ21 ▸ Subgroup.mem_map_of_mem _ hx
  have hτT12 : ∀ x ∈ T₁, τ x ∈ T₂ := fun x hx =>
    mem_inf.mpr ⟨h.τ_Q _ (mem_inf.mp hx).1, hτK12 _ (mem_inf.mp hx).2⟩
  have hτT21 : ∀ x ∈ T₂, τ x ∈ T₁ := fun x hx =>
    mem_inf.mpr ⟨h.τ_Q _ (mem_inf.mp hx).1, hτK21 _ (mem_inf.mp hx).2⟩
  have hcard12 : Nat.card T₁ ≤ Nat.card T₂ :=
    Nat.card_le_card_of_injective (fun x : T₁ => (⟨τ x, hτT12 x x.2⟩ : T₂))
      (fun a b hab => Subtype.ext (τ.injective (congrArg Subtype.val hab)))
  have hcard21 : Nat.card T₂ ≤ Nat.card T₁ :=
    Nat.card_le_card_of_injective (fun x : T₂ => (⟨τ x, hτT21 x x.2⟩ : T₁))
      (fun a b hab => Subtype.ext (τ.injective (congrArg Subtype.val hab)))
  have hTT : Nat.card T₂ = Nat.card T₁ := le_antisymm hcard21 hcard12
  have hTsup := h.card_sup_inf h₁ h₂ hne hZ₁
  have hTΩ : T₁ ⊔ T₂ ≤ gmiOmega Q :=
    sup_le (h.le_omega_of_sq h₁ le_rfl hT₁sq) (h.le_omega_of_sq h₂ le_rfl hT₂sq)
  have hTle := h.card_le_of_le_omega hcen hTΩ
  rw [hTsup, hTT] at hTle
  have hq4 := h.four_le
  have hTq : Nat.card T₁ = 2 ^ f ∧ ∃ (p n : ℕ) (_ : Fact p.Prime),
      (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
      Nonempty (K₁ ≃* PSL(2, GaloisField p n)) := by
    rcases hty₁ with ⟨he, -, hc⟩ | ⟨hf2, ⟨p, n, hp, hpodd, -, h8, he⟩, hc⟩ | ⟨hf2, -, hc⟩
    · exact ⟨hc, 2, f, ⟨Nat.prime_two⟩, Or.inl ⟨rfl, h.two_le⟩, he⟩
    · subst hf2
      refine ⟨by rw [hc]; norm_num, p, n, hp, Or.inr ⟨fun hp2 => ?_, h8⟩, he⟩
      rw [hp2] at hpodd
      exact absurd hpodd (by decide)
    · exfalso
      subst hf2
      rw [hc] at hTle
      norm_num at hTle
  obtain ⟨hTq, p, n, hp, hpn, hiso⟩ := hTq
  have hFeq : F = T₁ ⊔ T₂ := Subgroup.eq_of_le_of_card_ge hFT (by
    rw [hTsup, hTT, hTq, h.card_F, sq])
  have hFK₁ : F ⊓ K₁ = T₁ := by
    refine le_antisymm (le_inf (inf_le_left.trans h.F_le_Q) inf_le_right) (le_inf ?_ inf_le_right)
    rw [hFeq]
    exact le_sup_left
  have hK₂n := h.component_normal h₂
  set E₁ := K₁ ⊓ (Dv ⊔ K₂) with hE₁
  have hDdec : ∀ y ∈ Dv ⊔ K₂, ∃ d ∈ Dv, ∃ k ∈ K₂, d * k = y := fun y hy =>
    ncyc_exists_mul_of_mem_sup (fun z _ => gmi_top_le_normalizer hK₂n (mem_top z)) hy
  have hconj : ∀ g ∈ E₁, ∀ x ∈ F ⊓ K₁, g * x * g⁻¹ ∈ F ⊓ K₁ := by
    intro g hg x hx
    obtain ⟨d, hd, k, hk, hdk⟩ := hDdec g (mem_inf.mp hg).2
    have hkx : k * x = x * k := (mem_centralizer_iff.mp (hc21 hk) x (mem_inf.mp hx).2).symm
    rw [← hdk, show d * k * x * (d * k)⁻¹ = d * (k * x) * k⁻¹ * d⁻¹ by group, hkx,
      show d * (x * k) * k⁻¹ * d⁻¹ = d * x * d⁻¹ by group]
    exact mem_inf.mpr ⟨h.D_F d hd x (mem_inf.mp hx).1,
      (h.component_normal h₁).conj_mem x (mem_inf.mp hx).2 d⟩
  have hE₁N : E₁ ≤ normalizer ((F ⊓ K₁ : Subgroup X) : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj g hg x, fun hx => ?_⟩
    have := hconj g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  have hE₁odd : Odd (Nat.card E₁) := by
    have hE₁K₂ : E₁ ⊓ K₂ = ⊥ := by
      rw [eq_bot_iff, ← hK₁₂]
      exact inf_le_inf_right _ inf_le_left
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := K₂) (B := E₁) (fun x _ => gmi_top_le_normalizer hK₂n (mem_top x))
    rw [inf_comm, hE₁K₂, Subgroup.card_bot, mul_one] at h1
    have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := K₂) (B := Dv) (fun x _ => gmi_top_le_normalizer hK₂n (mem_top x))
    have hle : K₂ ⊔ E₁ ≤ K₂ ⊔ Dv := sup_le le_sup_left
      (inf_le_right.trans (by rw [sup_comm]))
    have h3 := Subgroup.card_dvd_of_le hle
    rw [h1] at h3
    have h4 : Nat.card K₂ * Nat.card E₁ * Nat.card (K₂ ⊓ Dv : Subgroup X) ∣
        Nat.card K₂ * Nat.card Dv := by
      rw [← h2]
      exact Nat.mul_dvd_mul_right h3 _
    rw [mul_assoc] at h4
    have h5 := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h4
    exact Odd.of_dvd_nat h.D_odd ((Dvd.intro _ rfl).trans h5)
  have hDE : ∀ d ∈ Dv, ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₁, d = e₁ * τ e₂ := by
    intro d hd
    have hdE : d ∈ K₁ ⊔ K₂ := hE ▸ h.K₀_le_layer (h.D_le hd)
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := h.mem_sup_dec h₂ hdE
    have hd₁E : d₁ ∈ E₁ := by
      refine mem_inf.mpr ⟨hd₁, ?_⟩
      rw [show d₁ = d₁ * d₂ * d₂⁻¹ by group]
      exact mul_mem (mem_sup_left hd) (mem_sup_right (inv_mem hd₂))
    have hτd := h.D_τ _ hd
    rw [map_mul] at hτd
    have hc : τ d₂ * τ d₁ = τ d₁ * τ d₂ :=
      (mem_centralizer_iff.mp (hc21 (hτK12 d₁ hd₁)) (τ d₂) (hτK21 d₂ hd₂))
    have hmem : d₁⁻¹ * τ d₂ ∈ K₁ ⊓ K₂ := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hd₁) (hτK21 d₂ hd₂), ?_⟩
      rw [show d₁⁻¹ * τ d₂ = d₂ * (τ d₁)⁻¹ by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hτd, ← hc, mul_inv_cancel_right]]
      exact mul_mem hd₂ (inv_mem (hτK12 d₁ hd₁))
    rw [hK₁₂, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    refine ⟨d₁, hd₁E, d₁, hd₁E, ?_⟩
    rw [hmem, h.τ_inv]
  refine ⟨K₁, E₁, p, n, hp, hpn, hiso, ?_, ?_, ?_, inf_le_left, hE₁N, hE₁odd, hDE⟩
  · intro a ha b hb
    exact (mem_centralizer_iff.mp (hc21 (hτK12 b hb)) a ha)
  · rw [hFK₁]
    exact h.isSylowOf_inf h₁
  · intro x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hFdec x hx
    refine ⟨x₁, hFK₁ ▸ hx₁, τ x₂, hFK₁ ▸ hτT21 x₂ hx₂, ?_⟩
    rw [h.τ_inv]

theorem ident (hC4 : GmiCatFourInput)
    (hCS : GmiCatSimpleInput) (hSchur : GmiCatSchurInput) :
    (∃ (K : Subgroup X) (p n : ℕ) (_ : Fact p.Prime),
        (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
        Nonempty (K ≃* PSL(2, GaloisField p n)) ∧ IsSylowOf 2 F K ∧ Dv ≤ K) ∨
    (∃ (K E₁ : Subgroup X) (p n : ℕ) (_ : Fact p.Prime),
      (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
      Nonempty (K ≃* PSL(2, GaloisField p n)) ∧
      (∀ a ∈ K, ∀ b ∈ K, a * τ b = τ b * a) ∧
      IsSylowOf 2 (F ⊓ K) K ∧
      (∀ x ∈ F, ∃ x₁ ∈ F ⊓ K, ∃ x₂ ∈ F ⊓ K, x = x₁ * τ x₂) ∧
      E₁ ≤ K ∧ E₁ ≤ normalizer ((F ⊓ K : Subgroup X) : Set X) ∧ Odd (Nat.card E₁) ∧
      ∀ d ∈ Dv, ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₁, d = e₁ * τ e₂) := by
  obtain ⟨K₁, h₁⟩ : ∃ K : Subgroup X, CFSG.IsComponent K := by
    by_contra hno
    push Not at hno
    have hbot : CFSG.layer X = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hno
    have hF : F = ⊥ := eq_bot_iff.mpr (hbot ▸ h.F_le_layer)
    have hc := h.card_F
    rw [hF, Subgroup.card_bot] at hc
    have := h.four_le
    nlinarith
  by_cases h2 : ∃ K₂ : Subgroup X, CFSG.IsComponent K₂ ∧ K₂ ≠ K₁
  · obtain ⟨K₂, h₂, hne⟩ := h2
    have hall : ∀ K : Subgroup X, CFSG.IsComponent K → K = K₁ ∨ K = K₂ := by
      intro K hK
      by_contra hno
      push Not at hno
      exact h.not_three_components hC4 hSchur h₁ h₂ hK hne hno.1 hno.2
    exact Or.inr (h.case_two hC4 hCS hSchur h₁ h₂ hne hall)
  · push Not at h2
    have hE : CFSG.layer X = K₁ :=
      le_antisymm (sSup_le fun K hK => (h2 K hK).le) (CFSG.LocalCores.component_le_layer h₁)
    obtain ⟨p, n, hp, hpn, hiso, hF, hD⟩ := h.case_one hC4 hCS hSchur h₁ hE
    exact Or.inl ⟨K₁, p, n, hp, hpn, hiso, hF, hD⟩

end GmiLayerHyp

end CFSG.SeitzReduction.RankOne
