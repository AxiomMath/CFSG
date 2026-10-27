module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2b
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

private theorem t_mul_comm_base {b : G} (hb : b ∈ baseGrp x₁ x₂) : t * b = b * t := by
  have h := t_comm_base hc hb
  calc t * b = t * b * t⁻¹ * t := by group
    _ = b * t := by rw [h]

private theorem base_le_N : baseGrp x₁ x₂ ≤ closure ({t, x₁, x₂} : Set G) := by
  rw [baseGrp]
  apply Subgroup.closure_mono
  rintro y (rfl | rfl) <;> simp

private theorem mem_N_decomp {n : G} (hn : n ∈ closure ({t, x₁, x₂} : Set G)) :
    ∃ b ∈ baseGrp x₁ x₂, n = b ∨ n = b * t := by
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · exact ⟨1, one_mem _, Or.inr (by rw [hx, one_mul])⟩
      · exact ⟨x₁, subset_closure (by simp), Or.inl hx⟩
      · exact ⟨x₂, subset_closure (by simp), Or.inl hx⟩
  | one => exact ⟨1, one_mem _, Or.inl rfl⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨b₁, hb₁, h₁⟩ := ihx
      obtain ⟨b₂, hb₂, h₂⟩ := ihy
      refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, ?_⟩
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · left; rw [h₁, h₂]
      · right; rw [h₁, h₂]; group
      · right
        rw [h₁, h₂]
        calc b₁ * t * b₂ = b₁ * (t * b₂) := by group
          _ = b₁ * (b₂ * t) := by rw [t_mul_comm_base hc hb₂]
          _ = b₁ * b₂ * t := by group
      · left
        rw [h₁, h₂]
        calc b₁ * t * (b₂ * t) = b₁ * (t * b₂) * t := by group
          _ = b₁ * (b₂ * t) * t := by rw [t_mul_comm_base hc hb₂]
          _ = b₁ * b₂ * (t * t) := by group
          _ = b₁ * b₂ := by rw [hc.t_mul_self, mul_one]
  | inv x _ ihx =>
      obtain ⟨b, hb, h⟩ := ihx
      refine ⟨b⁻¹, inv_mem hb, ?_⟩
      rcases h with h | h
      · left; rw [h]
      · right
        rw [h]
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hc.t_mul_self
        calc (b * t)⁻¹ = t⁻¹ * b⁻¹ := by group
          _ = t * b⁻¹ := by rw [htinv]
          _ = b⁻¹ * t := t_mul_comm_base hc (inv_mem hb)

theorem N_le_CO : closure ({t, x₁, x₂} : Set G) ≤
    ctxO t tau x₁ x₂ ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  rw [closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg | hg
  · rw [hg]
    refine Subgroup.mem_inf.mpr ⟨hc.t_mem_O, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (t_mul_comm_base hc hk).symm
  · rw [hg]
    refine Subgroup.mem_inf.mpr ⟨hc.Q_le_O (hc.base_le_Q (subset_closure (by simp))), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact base_comm hc k hk x₁ (subset_closure (by simp))
  · rw [hg]
    refine Subgroup.mem_inf.mpr ⟨hc.Q_le_O (hc.base_le_Q (subset_closure (by simp))), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact base_comm hc k hk x₂ (subset_closure (by simp))

theorem not_three_dvd_N : ¬ 3 ∣ Nat.card (closure ({t, x₁, x₂} : Set G)) := by
  intro h3
  have hdvd : Nat.card (closure ({t, x₁, x₂} : Set G)) ∣ 2 ^ 8 := by
    have h := Subgroup.card_dvd_of_le (le_trans (N_le_CO hc) inf_le_left)
    rwa [hc.card_O] at h
  exact absurd (h3.trans hdvd) (by norm_num)

theorem rho_norm_N : ∀ n ∈ closure ({t, x₁, x₂} : Set G), rho * n * rho⁻¹ ∈
    closure ({t, x₁, x₂} : Set G) := by
  refine conj_mem_closure (S := ({t, x₁, x₂} : Set G)) ?_
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with hs | hs | hs
  · have h : rho * t * rho⁻¹ = t := by rw [hc.rho_comm_t]; group
    rw [hs, h]; exact subset_closure (by simp)
  · rw [hs]; exact base_le_N hc (rho_norm_base hc x₁ (subset_closure (by simp)))
  · rw [hs]; exact base_le_N hc (rho_norm_base hc x₂ (subset_closure (by simp)))

theorem inv_base_of {u : G} (hu : u = tau ∨ u = t * tau) :
    ∀ k ∈ baseGrp x₁ x₂, u * k * u⁻¹ = k⁻¹ := by
  intro k hk
  rcases hu with hu | hu
  · rw [hu]; exact tau_inv_base hc k hk
  · rw [hu]
    have h := tau_inv_base hc k hk
    calc (t * tau) * k * (t * tau)⁻¹ = t * (tau * k * tau⁻¹) * t⁻¹ := by group
      _ = t * k⁻¹ * t⁻¹ := by rw [h]
      _ = k⁻¹ := t_comm_base hc (inv_mem hk)

theorem not_centralizes_x₁ {u : G} (hu : u = tau ∨ u = t * tau) : u * x₁ * u⁻¹ ≠ x₁ := by
  intro h
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := subset_closure (by simp)
  have h2 : x₁ = x₁⁻¹ := by
    have := inv_base_of hc hu x₁ hx₁
    rwa [h] at this
  have hx₁sq : x₁ * x₁ = 1 := by
    have hh := congrArg (fun y => y * x₁) h2
    simpa using hh
  have hdvd : orderOf x₁ ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hx₁sq)
  rw [hc.wreath.ord_x₁] at hdvd
  norm_num at hdvd

private theorem contradiction_of_decomp
    (hCQ : ctxQ t tau x₁ x₂ rho ⊓
      centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) = baseGrp x₁ x₂)
    {k q u : G} (hkO : k ∈ ctxO t tau x₁ x₂)
    (hkC : k ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G))
    (hqQ : q ∈ ctxQ t tau x₁ x₂ rho)
    (huT : u ∈ closure ({t, tau} : Set G))
    (hk_eq : k = q * u)
    (hu : u = tau ∨ u = t * tau) : False := by
  have hAN : baseGrp x₁ x₂ ≤ closure ({t, x₁, x₂} : Set G) := base_le_N hc
  have hN_le_O : closure ({t, x₁, x₂} : Set G) ≤ ctxO t tau x₁ x₂ :=
    (N_le_CO hc).trans inf_le_left
  have hN_le_C : closure ({t, x₁, x₂} : Set G) ≤
      centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    (N_le_CO hc).trans inf_le_right
  have huM : u ∈ ctxM t tau x₁ x₂ := T_le_M hc huT
  have hrho_u : rho * u * rho⁻¹ = u := by
    rcases hu with h | h
    · rw [h]; rw [hc.rho_comm_tau]; group
    · rw [h]
      have h1 : rho * t * rho⁻¹ = t := by rw [hc.rho_comm_t]; group
      have h2 : rho * tau * rho⁻¹ = tau := by rw [hc.rho_comm_tau]; group
      calc rho * (t * tau) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * tau * rho⁻¹) := by group
        _ = t * tau := by rw [h1, h2]
  have hk'O : rho * k * rho⁻¹ ∈ ctxO t tau x₁ x₂ :=
    (O_normal_M t tau x₁ x₂).2 rho hc.rho_mem_M k hkO
  have hk'C : rho * k * rho⁻¹ ∈
      centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hrhoinv_norm : rho⁻¹ ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
      inv_mem (Subgroup.mem_normalizer_fintype (fun b hb => rho_norm_base hc b hb))
    have ha' : rho⁻¹ * a * rho ∈ baseGrp x₁ x₂ :=
      by simpa using (Subgroup.mem_normalizer_iff.mp hrhoinv_norm a).mp ha
    have hcomm := Subgroup.mem_centralizer_iff.mp hkC (rho⁻¹ * a * rho) ha'
    calc a * (rho * k * rho⁻¹)
        = rho * ((rho⁻¹ * a * rho) * k) * rho⁻¹ := by group
      _ = rho * (k * (rho⁻¹ * a * rho)) * rho⁻¹ := by rw [hcomm]
      _ = (rho * k * rho⁻¹) * a := by group
  have hq'Q : rho * q * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.normal_Q.2 rho hc.rho_mem_M q hqQ
  have hrho_step : rho * (q * u) * rho⁻¹ = (rho * q * rho⁻¹) * u := by
    calc rho * (q * u) * rho⁻¹ = (rho * q * rho⁻¹) * (rho * u * rho⁻¹) := by group
      _ = (rho * q * rho⁻¹) * u := by rw [hrho_u]
  have hwQ : k⁻¹ * rho * k * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    have hw_eq : k⁻¹ * rho * k * rho⁻¹ =
        u⁻¹ * (q⁻¹ * (rho * q * rho⁻¹)) * u := by
      calc k⁻¹ * rho * k * rho⁻¹
          = k⁻¹ * (rho * k * rho⁻¹) := by group
        _ = (q * u)⁻¹ * (rho * (q * u) * rho⁻¹) := by rw [hk_eq]
        _ = (q * u)⁻¹ * ((rho * q * rho⁻¹) * u) := by rw [hrho_step]
        _ = u⁻¹ * (q⁻¹ * (rho * q * rho⁻¹)) * u := by group
    rw [hw_eq]
    have hqq' : q⁻¹ * (rho * q * rho⁻¹) ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem (inv_mem hqQ) hq'Q
    have h := hc.normal_Q.2 u⁻¹ (inv_mem huM) (q⁻¹ * (rho * q * rho⁻¹)) hqq'
    simpa using h
  have hwC : k⁻¹ * rho * k * rho⁻¹ ∈
      centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [show k⁻¹ * rho * k * rho⁻¹ = k⁻¹ * (rho * k * rho⁻¹) by group]
    exact mul_mem (inv_mem hkC) hk'C
  have hwA : k⁻¹ * rho * k * rho⁻¹ ∈ baseGrp x₁ x₂ := by
    rw [← hCQ]
    exact Subgroup.mem_inf.mpr ⟨hwQ, hwC⟩
  have hwN : k⁻¹ * rho * k * rho⁻¹ ∈ closure ({t, x₁, x₂} : Set G) := hAN hwA
  have hrho3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  obtain ⟨n, hnN, hnfix⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.Prod.exists_fixed_coset
      (closure ({t, x₁, x₂} : Set G)) rho k hrho3 (rho_norm_N hc) hwN (not_three_dvd_N hc)
  have hk₂O : k * n ∈ ctxO t tau x₁ x₂ := mul_mem hkO (hN_le_O hnN)
  have hk₂C : k * n ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    mul_mem hkC (hN_le_C hnN)
  have hk₂T : k * n ∈ closure ({t, tau} : Set G) := by
    have hCO : k * n ∈ ctxCO t tau x₁ x₂ rho := by
      refine Subgroup.mem_inf.mpr ⟨hk₂O, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hnfix.symm
    rwa [hc.CO_rho] at hCO
  obtain ⟨b, hbA, hbcase⟩ := mem_N_decomp hc hnN
  have hex : ∃ q'' ∈ ctxQ t tau x₁ x₂ rho, ∃ s'' ∈ closure ({t, tau} : Set G),
      k * n = q'' * s'' ∧ (s'' = tau ∨ s'' = t * tau) := by
    rcases hbcase with hb | hb
    · refine ⟨q * (u * b * u⁻¹),
        mul_mem hqQ (hc.normal_Q.2 u huM b (hc.base_le_Q hbA)), u, huT, ?_, hu⟩
      rw [hk_eq, hb]
      group
    · refine ⟨q * (u * b * u⁻¹),
        mul_mem hqQ (hc.normal_Q.2 u huM b (hc.base_le_Q hbA)),
        u * t, mul_mem huT (subset_closure (by simp)), ?_, ?_⟩
      · rw [hk_eq, hb]
        group
      · rcases hu with h | h
        · right; rw [h]; exact hc.t_comm_tau.symm
        · left
          rw [h]
          calc (t * tau) * t = t * (tau * t) := by group
            _ = t * (t * tau) := by rw [hc.t_comm_tau]
            _ = (t * t) * tau := by group
            _ = tau := by rw [hc.t_mul_self, one_mul]
  obtain ⟨q'', hq''Q, s'', hs''T, hk₂_eq, hs''case⟩ := hex
  have hq''T : q'' ∈ closure ({t, tau} : Set G) := by
    have hq'' : q'' = (k * n) * s''⁻¹ := by rw [hk₂_eq]; group
    rw [hq'']
    exact mul_mem hk₂T (inv_mem hs''T)
  have hq''1 : q'' = 1 := by
    have hbot : q'' ∈ (⊥ : Subgroup G) := by
      rw [← Q_inf_T hc]
      exact Subgroup.mem_inf.mpr ⟨hq''Q, hq''T⟩
    exact Subgroup.mem_bot.mp hbot
  have hk₂_s'' : k * n = s'' := by rw [hk₂_eq, hq''1, one_mul]
  have hk₂_case : k * n = tau ∨ k * n = t * tau := by
    rw [hk₂_s'']; exact hs''case
  have hx₁A : x₁ ∈ baseGrp x₁ x₂ := subset_closure (by simp)
  have hx₁k₂ : x₁ * (k * n) = (k * n) * x₁ :=
    Subgroup.mem_centralizer_iff.mp hk₂C x₁ hx₁A
  have hfix : (k * n) * x₁ * (k * n)⁻¹ = x₁ := by rw [← hx₁k₂]; group
  exact (not_centralizes_x₁ hc hk₂_case) hfix

theorem CO_le_N (hCQ : ctxQ t tau x₁ x₂ rho ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
      baseGrp x₁ x₂) :
    ctxO t tau x₁ x₂ ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) ≤
      closure ({t, x₁, x₂} : Set G) := by
  intro k hk
  rw [Subgroup.mem_inf] at hk
  obtain ⟨hkO, hkC⟩ := hk
  obtain ⟨q, hqQ, s, hsT, hk_eq⟩ := O_decomp hc hkO
  have hAN : baseGrp x₁ x₂ ≤ closure ({t, x₁, x₂} : Set G) := base_le_N hc
  have htC : t ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (t_mul_comm_base hc ha).symm
  have memA : ∀ {x : G}, x ∈ ctxQ t tau x₁ x₂ rho →
      x ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) → x ∈ baseGrp x₁ x₂ := by
    intro x hxQ hxC
    rw [← hCQ]
    exact Subgroup.mem_inf.mpr ⟨hxQ, hxC⟩
  rcases (mem_T_iff hc).mp hsT with hs | hs | hs | hs
  · have hkq : k = q := by rw [hk_eq, hs, mul_one]
    have hqC : q ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hkq]; exact hkC
    rw [hkq]
    exact hAN (memA hqQ hqC)
  · have hq_eq : q = k * t⁻¹ := by rw [hk_eq, hs]; group
    have hqC : q ∈ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [hq_eq]; exact mul_mem hkC (inv_mem htC)
    rw [hk_eq, hs]
    exact mul_mem (hAN (memA hqQ hqC)) (subset_closure (by simp))
  · exact (contradiction_of_decomp hc hCQ hkO hkC hqQ hsT hk_eq (Or.inl hs)).elim
  · exact (contradiction_of_decomp hc hCQ hkO hkC hqQ hsT hk_eq (Or.inr hs)).elim

theorem CO_base_holds (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) :
    ctxO t tau x₁ x₂ ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
      closure {t, x₁, x₂} := by
  exact le_antisymm (CO_le_N hc (CQ_base_eq hc hs)) (N_le_CO hc)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
