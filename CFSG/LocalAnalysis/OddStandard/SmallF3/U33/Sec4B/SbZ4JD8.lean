module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IS0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Mc_fusion {σ : H} (hσ2 : σ * σ = 1) (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹) (hσMh : σ ∉ Mh)
    (hσMc : ∀ x ∈ Mc, σ * x * σ⁻¹ ∈ Mc) :
    (∀ m ∈ Mc, σ * m * (σ * m) = 1 → ∃ w ∈ Mc, σ * m = w * σ * w⁻¹) ∧
      Nat.card ↥(Mc ⊓ centralizer ({σ} : Set H)) = 16 := by
  classical
  have hσne : σ ≠ 1 := by
    intro h1
    apply hσMh
    rw [h1]
    exact Mh.one_mem
  have hord : orderOf σ = 2 :=
    orderOf_eq_prime (p := 2) (by rwa [pow_two]) hσne
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hQMc : Q ≤ Mc := h.Q_le_Mc hMh hMc
  have hMcMh : Mc ≤ Mh := h.Mc_le_Mh hMh hMc
  have hcom_McQ : ∀ x ∈ Mc, ∀ y ∈ Mc, x * y * x⁻¹ * y⁻¹ ∈ Q :=
    fun x hx y hy => h.Mh_comm_mem_Q hMh (hMcMh hx) (hMcMh hy)
  have hsq_McQ : ∀ x ∈ Mc, x ^ 2 ∈ Q :=
    fun x hx => by rw [pow_two]; exact h.Mh_sq_mem_Q hMh (hMcMh hx)
  have hcom_QY : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Y := by
    intro x hx y hy
    rw [h.Q_comm x hx y hy]
    have h1 : y * x * x⁻¹ * y⁻¹ = 1 := by group
    rw [h1]
    exact Y.one_mem
  have hsq_QY : ∀ x ∈ Q, x ^ 2 ∈ Y := fun x hx => hVY (h.sq_mem_V x hx)
  have hcom_YV : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ V := by
    intro x hx y hy
    rw [h.Q_comm x (h.Y_le_Q hx) y (h.Y_le_Q hy)]
    have h1 : y * x * x⁻¹ * y⁻¹ = 1 := by group
    rw [h1]
    exact V.one_mem
  have hsq_YV : ∀ x ∈ Y, x ^ 2 ∈ V := by
    intro x hx
    rw [pow_two, h.Y_sq x hx]
    exact V.one_mem
  have hcom_Vbot : ∀ x ∈ V, ∀ y ∈ V, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup H) := by
    intro x hx y hy
    rw [h.Q_comm x (h.Y_le_Q (hVY hx)) y (h.Y_le_Q (hVY hy))]
    refine Subgroup.mem_bot.mpr ?_
    show y * x * x⁻¹ * y⁻¹ = 1
    group
  have hsq_Vbot : ∀ x ∈ V, x ^ 2 ∈ (⊥ : Subgroup H) := by
    intro x hx
    refine Subgroup.mem_bot.mpr ?_
    rw [pow_two, h.Y_sq x (hVY hx)]
  have hreg0 : ActsRegularly σ Q Mc :=
    z4i_s3_regular h.rho_pow_three hσ2 hσρ hQMc hcom_McQ hsq_McQ
      h.rho_norm_Q (fun x hx => h.Mc_conj_rho hMh hMc hx)
      (fun n hn => h.normal_Q σ n hn) hσMc
      (fun x hx hc => h.Mc_fpf_Q hMh hMc hx hc)
  have hreg1 : ActsRegularly σ Y Q :=
    z4i_s3_regular h.rho_pow_three hσ2 hσρ h.Y_le_Q hcom_QY hsq_QY
      h.rho_norm_Y h.rho_norm_Q
      (fun n hn => h.normal_Y σ n hn) (fun n hn => h.normal_Q σ n hn)
      (fun x hx hc => h.Mc_fpf_Y hMh hMc (hQMc hx) hc)
  have hreg2 : ActsRegularly σ V Y :=
    z4i_s3_regular h.rho_pow_three hσ2 hσρ hVY hcom_YV hsq_YV
      h.rho_norm_V h.rho_norm_Y
      (fun n hn => h.normal_V σ n hn) (fun n hn => h.normal_Y σ n hn)
      (fun x hx hc => h.Mc_fpf_V hMh hMc (hQMc (h.Y_le_Q hx)) hc)
  have hreg3 : ActsRegularly σ ⊥ V :=
    z4i_s3_regular h.rho_pow_three hσ2 hσρ bot_le hcom_Vbot hsq_Vbot
      (fun n hn => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hn]; group))
      h.rho_norm_V
      (fun n hn => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hn]; group))
      (fun n hn => h.normal_V σ n hn)
      (fun x hx hc => by
        refine Subgroup.mem_bot.mpr ?_
        have hfix : ρ * x * ρ⁻¹ = x := eq_of_mul_inv_eq_one (Subgroup.mem_bot.mp hc)
        exact h.rho_fpf_Q x (h.Y_le_Q (hVY hx)) hfix)
  let W : ℕ → Subgroup H := fun i =>
    match i with
    | 0 => Mc
    | 1 => Q
    | 2 => Y
    | 3 => V
    | _ => ⊥
  have hle : ∀ i < 4, W (i + 1) ≤ W i := by
    intro i hi
    interval_cases i
    · simp only [W]
      exact hQMc
    · simp only [W]
      exact h.Y_le_Q
    · simp only [W]
      exact hVY
    · simp only [W]
      exact bot_le
  have htnorm : ∀ i ≤ 4, ∀ g ∈ W i, σ * g * σ⁻¹ ∈ W i := by
    intro i hi g hg
    interval_cases i
    · simp only [W] at hg ⊢
      exact hσMc g hg
    · simp only [W] at hg ⊢
      exact h.normal_Q σ g hg
    · simp only [W] at hg ⊢
      exact h.normal_Y σ g hg
    · simp only [W] at hg ⊢
      exact h.normal_V σ g hg
    · simp only [W] at hg ⊢
      exact Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hg]; group)
  have hcomm : ∀ i < 4, ∀ x ∈ W i, ∀ y ∈ W i, ⁅x, y⁆ ∈ W (i + 1) := by
    intro i hi x hx y hy
    interval_cases i
    · simp only [W] at hx hy ⊢
      exact hcom_McQ x hx y hy
    · simp only [W] at hx hy ⊢
      exact hcom_QY x hx y hy
    · simp only [W] at hx hy ⊢
      exact hcom_YV x hx y hy
    · simp only [W] at hx hy ⊢
      exact hcom_Vbot x hx y hy
  have hsq : ∀ i < 4, ∀ x ∈ W i, x ^ 2 ∈ W (i + 1) := by
    intro i hi x hx
    interval_cases i
    · simp only [W] at hx ⊢
      exact hsq_McQ x hx
    · simp only [W] at hx ⊢
      exact hsq_QY x hx
    · simp only [W] at hx ⊢
      exact hsq_YV x hx
    · simp only [W] at hx ⊢
      exact hsq_Vbot x hx
  have hreg : ∀ i < 4, ActsRegularly σ (W (i + 1)) (W i) := by
    intro i hi
    interval_cases i
    · simpa only [W] using hreg0
    · simpa only [W] using hreg1
    · simpa only [W] using hreg2
    · simpa only [W] using hreg3
  obtain ⟨hset, hcard⟩ := lemma36 Mc σ hord 4 W rfl rfl hle htnorm hcomm hsq hreg
  constructor
  · intro m hm hsm
    have hne : σ * m ≠ 1 := by
      intro h1
      apply hσMh
      have h2 : σ = m⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact hMcMh (Mc.inv_mem hm)
    have hordm : orderOf (σ * m) = 2 :=
      orderOf_eq_prime (p := 2) (by rwa [pow_two]) hne
    have hmem : σ * m ∈ {j : H | (∃ s ∈ Mc, j = σ * s) ∧ orderOf j = 2} :=
      ⟨⟨m, hm, rfl⟩, hordm⟩
    rw [hset] at hmem
    exact hmem
  · have hcm : Nat.card Mc = 256 := h.card_Mc hMh hMc
    have h2 : Nat.card ↥(Mc ⊓ centralizer ({σ} : Set H)) ^ 2 = 16 ^ 2 := by
      rw [hcard, hcm]
      norm_num
    exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h2

theorem Mc_fusion_l :
    (∀ m ∈ Mc, l * m * (l * m) = 1 → ∃ w ∈ Mc, l * m = w * l * w⁻¹) ∧
      Nat.card ↥(Mc ⊓ centralizer ({l} : Set H)) = 16 := by
  exact h.Mc_fusion (σ := l) hMh hMc h.l_sq h.l_rho
    (h.l_not_mem_Mh hMh) (fun x hx => h.Mc_conj_l hMh hMc hx)

theorem Mc_fusion_lt :
    (∀ m ∈ Mc, l * t * m * (l * t * m) = 1 → ∃ w ∈ Mc, l * t * m = w * (l * t) * w⁻¹) ∧
      Nat.card ↥(Mc ⊓ centralizer ({l * t} : Set H)) = 16 := by
  have hσ2 : (l * t) * (l * t) = 1 := by
    have hcl : Commute l t := h.t_l.symm
    have h1 := hcl.mul_pow 2
    simp only [pow_two] at h1
    rw [h1, h.l_sq, h.t_sq, mul_one]
  have hσρ : (l * t) * ρ * (l * t)⁻¹ = ρ⁻¹ := by
    have htρ : t * ρ * t⁻¹ = ρ := by rw [h.t_rho]; group
    rw [show (l * t) * ρ * (l * t)⁻¹ = l * (t * ρ * t⁻¹) * l⁻¹ by group, htρ, h.l_rho]
  have hσMh : l * t ∉ Mh := by
    rw [← h.t_l]
    exact h.tl_not_mem_Mh hMh
  have hσMc : ∀ x ∈ Mc, (l * t) * x * (l * t)⁻¹ ∈ Mc := by
    intro x hx
    rw [show (l * t) * x * (l * t)⁻¹ = l * (t * x * t⁻¹) * l⁻¹ by group]
    exact h.Mc_conj_l hMh hMc (h.Mc_conj_t hMh hMc hx)
  exact h.Mc_fusion (σ := l * t) hMh hMc hσ2 hσρ hσMh hσMc

theorem Mc_fusion_ltau :
    (∀ m ∈ Mc, l * τ * m * (l * τ * m) = 1 → ∃ w ∈ Mc, l * τ * m = w * (l * τ) * w⁻¹) ∧
      Nat.card ↥(Mc ⊓ centralizer ({l * τ} : Set H)) = 16 := by
  have hσ2 : (l * τ) * (l * τ) = 1 := by
    have hcl : Commute l τ := h.tau_l.symm
    have h1 := hcl.mul_pow 2
    simp only [pow_two] at h1
    rw [h1, h.l_sq, h.tau_sq, mul_one]
  have hσρ : (l * τ) * ρ * (l * τ)⁻¹ = ρ⁻¹ := by
    have hτρ : τ * ρ * τ⁻¹ = ρ := by rw [h.tau_rho]; group
    rw [show (l * τ) * ρ * (l * τ)⁻¹ = l * (τ * ρ * τ⁻¹) * l⁻¹ by group, hτρ, h.l_rho]
  have hσMh : l * τ ∉ Mh := by
    intro hmem
    have hτ : τ ∈ Mh := h.tau_mem_Mh hMh
    have hl : l ∈ Mh := by
      have h1 := Mh.mul_mem hmem (Mh.inv_mem hτ)
      rwa [show (l * τ) * τ⁻¹ = l by group] at h1
    exact h.l_not_mem_Mh hMh hl
  have hσMc : ∀ x ∈ Mc, (l * τ) * x * (l * τ)⁻¹ ∈ Mc := by
    intro x hx
    rw [show (l * τ) * x * (l * τ)⁻¹ = l * (τ * x * τ⁻¹) * l⁻¹ by group]
    exact h.Mc_conj_l hMh hMc (h.Mc_conj_tau hMh hMc hx)
  exact h.Mc_fusion (σ := l * τ) hMh hMc hσ2 hσρ hσMh hσMc

theorem Mc_fusion_lttau :
    (∀ m ∈ Mc, l * t * τ * m * (l * t * τ * m) = 1 →
        ∃ w ∈ Mc, l * t * τ * m = w * (l * t * τ) * w⁻¹) ∧
      Nat.card ↥(Mc ⊓ centralizer ({l * t * τ} : Set H)) = 16 := by
  have hσ2 : (l * t * τ) * (l * t * τ) = 1 := by
    have hclt : Commute l t := h.t_l.symm
    have hctt : Commute t τ := h.t_tau
    have hcl : Commute l (t * τ) := hclt.mul_right (show Commute l τ from h.tau_l.symm)
    have h1 := hcl.mul_pow 2
    have h2 := hctt.mul_pow 2
    simp only [pow_two] at h1 h2
    rw [show (l * t * τ) * (l * t * τ) = (l * (t * τ)) * (l * (t * τ)) by group,
      h1, h2, h.l_sq, h.t_sq, h.tau_sq]
    group
  have hσρ : (l * t * τ) * ρ * (l * t * τ)⁻¹ = ρ⁻¹ := by
    have htρ : t * ρ * t⁻¹ = ρ := by rw [h.t_rho]; group
    have hτρ : τ * ρ * τ⁻¹ = ρ := by rw [h.tau_rho]; group
    rw [show (l * t * τ) * ρ * (l * t * τ)⁻¹
        = l * (t * (τ * ρ * τ⁻¹) * t⁻¹) * l⁻¹ by group, hτρ, htρ, h.l_rho]
  have hσMh : l * t * τ ∉ Mh := by
    intro hmem
    have hτ : τ ∈ Mh := h.tau_mem_Mh hMh
    have hlt : l * t ∈ Mh := by
      have h1 := Mh.mul_mem hmem (Mh.inv_mem hτ)
      rwa [show (l * t * τ) * τ⁻¹ = l * t by group] at h1
    exact h.tl_not_mem_Mh hMh (by simpa [h.t_l] using hlt)
  have hσMc : ∀ x ∈ Mc, (l * t * τ) * x * (l * t * τ)⁻¹ ∈ Mc := by
    intro x hx
    rw [show (l * t * τ) * x * (l * t * τ)⁻¹
        = l * (t * (τ * x * τ⁻¹) * t⁻¹) * l⁻¹ by group]
    exact h.Mc_conj_l hMh hMc (h.Mc_conj_t hMh hMc (h.Mc_conj_tau hMh hMc hx))
  exact h.Mc_fusion (σ := l * t * τ) hMh hMc hσ2 hσρ hσMh hσMc

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
