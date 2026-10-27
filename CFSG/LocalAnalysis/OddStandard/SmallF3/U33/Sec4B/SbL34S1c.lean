module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section Decomp

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau)
include hc

theorem O_decomp {a : G} (ha : a ∈ ctxO t tau x₁ x₂) :
    ∃ b ∈ ctxQ t tau x₁ x₂ rho, ∃ s ∈ closure ({t, tau} : Set G), a = b * s := by
  have hT_le_M : closure ({t, tau} : Set G) ≤ ctxM t tau x₁ x₂ := by
    rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hc.toCtx4Q.t_mem_M
    · rw [hx]; exact hc.toCtx4Q.tau_mem_M
  have hT_le_norm :
      closure ({t, tau} : Set G) ≤ Subgroup.normalizer (ctxQ t tau x₁ x₂ rho) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs k hk
    exact hc.normal_Q.2 s (hT_le_M hs) k hk
  have ha' : a ∈ closure ({t, tau} : Set G) ⊔ ctxQ t tau x₁ x₂ rho := by
    rw [sup_comm, ← hc.O_eq_Q]
    exact ha
  have ha'' : a ∈ (closure ({t, tau} : Set G) : Set G) * (ctxQ t tau x₁ x₂ rho : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT_le_norm]
    exact ha'
  rw [Set.mem_mul] at ha''
  obtain ⟨s, hs, b, hb, hsb⟩ := ha''
  refine ⟨s * b * s⁻¹, ?_, s, hs, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hT_le_norm hs) b).mp hb
  · rw [← hsb]
    group

theorem T_comm_q {s : G} (hs : s ∈ closure ({t, tau} : Set G)) :
    (t * lam) * s = s * (t * lam) := by
  have ht : t ∈ centralizer ({t * lam} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc (t * lam) * t = t * (lam * t) := by group
      _ = t * (t * lam) := by rw [← t_comm_lam hc.toCtx4Q]
  have htau : tau ∈ centralizer ({t * lam} : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact q_comm_tau hc.toCtx4Q
  have h : closure ({t, tau} : Set G) ≤ centralizer ({t * lam} : Set G) := by
    rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact ht
    · rw [hx]; exact htau
  exact Subgroup.mem_centralizer_iff.mp (h hs) (t * lam) (by simp)

theorem q_conj_Q {a : G} (ha : a ∈ ctxQ t tau x₁ x₂ rho) :
    (t * lam) * a * (t * lam)⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  hc.normal_Q.2 _ (q_mem_M hc) a ha

theorem Q_inf_X_le_V {x : G} (hxQ : x ∈ ctxQ t tau x₁ x₂ rho) (hxX : x ∈ ctxX t tau x₁ x₂) :
    x ∈ fourGrp x₁ x₂ := by
  rcases S4A.mem_ctxX_cases hc.toCtx hc.l44.1 hxX with hV | hV | hV | hV
  · exact hV
  · rw [Set.mem_smul_set] at hV
    obtain ⟨f, hf, hfu⟩ := hV
    exfalso
    apply hc.toCtx4Q.t_not_mem_Q
    have ht : t = x * f⁻¹ := by
      rw [smul_eq_mul] at hfu
      exact eq_mul_inv_of_mul_eq hfu
    have hmem : x * f⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hxQ (inv_mem (hc.toCtx4Q.V_le_Q hf))
    rwa [← ht] at hmem
  · rw [Set.mem_smul_set] at hV
    obtain ⟨f, hf, hfu⟩ := hV
    exfalso
    apply hc.toCtx4Q.tau_not_mem_Q
    have htau : tau = x * f⁻¹ := by
      rw [smul_eq_mul] at hfu
      exact eq_mul_inv_of_mul_eq hfu
    have hmem : x * f⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hxQ (inv_mem (hc.toCtx4Q.V_le_Q hf))
    rwa [← htau] at hmem
  · rw [Set.mem_smul_set] at hV
    obtain ⟨f, hf, hfu⟩ := hV
    exfalso
    apply hc.toCtx4Q.ttau_not_mem_Q
    have httau : t * tau = x * f⁻¹ := by
      rw [smul_eq_mul] at hfu
      exact eq_mul_inv_of_mul_eq hfu
    have hmem : x * f⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hxQ (inv_mem (hc.toCtx4Q.V_le_Q hf))
    rwa [← httau] at hmem

theorem V_comm_O {a u : G} (ha : a ∈ ctxO t tau x₁ x₂) (hu : u ∈ fourGrp x₁ x₂) :
    a * u = u * a := by
  have hu' : u ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [hc.Z_O]
    exact hu
  exact Subgroup.mem_centralizer_iff.mp hu'.2 a ha

end Decomp

section Fix

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau)
include hc

theorem fix_cases {a : G} (ha : a ∈ ctxO t tau x₁ x₂)
    (hX : (t * lam) * a * (t * lam)⁻¹ * a⁻¹ ∈ ctxX t tau x₁ x₂) :
    (t * lam) * a = a * (t * lam) ∨ (t * lam) * (a * x₁ ^ 2) = (a * x₁ ^ 2) * (t * lam) := by
  obtain ⟨b, hb, s, hs, ha_eq⟩ := O_decomp hc ha
  let q : G := t * lam
  change q * a = a * q ∨ q * (a * x₁ ^ 2) = (a * x₁ ^ 2) * q
  change q * a * q⁻¹ * a⁻¹ ∈ ctxX t tau x₁ x₂ at hX
  have hqs : q * s = s * q := T_comm_q hc hs
  have hq2 : q * q = 1 := q_mul_self hc.toCtx4Q
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := y_mul_self hc.toCtx4Q
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := z_mul_self hc.toCtx4Q
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := y_comm_z hc.toCtx4Q
  have hqy : q * x₁ ^ 2 * q⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := q_conj_y hc.toCtx4Q
  have hqz : q * (x₁ * x₂) ^ 2 * q⁻¹ = (x₁ * x₂) ^ 2 := q_conj_z hc.toCtx4Q
  let u : G := q * b * q⁻¹ * b⁻¹
  have hcomm : q * a * q⁻¹ * a⁻¹ = u := by
    change q * a * q⁻¹ * a⁻¹ = q * b * q⁻¹ * b⁻¹
    rw [ha_eq, hqinv]
    calc q * (b * s) * q * (b * s)⁻¹
        = q * b * (s * q) * s⁻¹ * b⁻¹ := by group
      _ = q * b * (q * s) * s⁻¹ * b⁻¹ := by rw [← hqs]
      _ = q * b * q * (s * s⁻¹) * b⁻¹ := by group
      _ = q * b * q * b⁻¹ := by group
  have huX : u ∈ ctxX t tau x₁ x₂ := hcomm ▸ hX
  have huQ : u ∈ ctxQ t tau x₁ x₂ rho :=
    mul_mem (q_conj_Q hc hb) (inv_mem hb)
  have huV : u ∈ fourGrp x₁ x₂ := Q_inf_X_le_V hc huQ huX
  have hu2 : u * u = 1 := by
    have h := (fourGrp_elemAbelian hc.toCtx4Q).2 u huV
    rwa [pow_two] at h
  have hqb : q * b * q⁻¹ = u * b := by
    change q * b * q⁻¹ = (q * b * q⁻¹ * b⁻¹) * b
    group
  have hb_eq : b = (q * u * q⁻¹) * (u * b) := by
    have h1 : q * (q * b * q⁻¹) * q⁻¹ = b := by
      rw [hqinv]
      calc q * (q * b * q) * q = (q * q) * b * (q * q) := by group
        _ = b := by rw [hq2]; group
    calc b = q * (q * b * q⁻¹) * q⁻¹ := h1.symm
      _ = q * (u * b) * q⁻¹ := by rw [← hqb]
      _ = (q * u * q⁻¹) * (q * b * q⁻¹) := by group
      _ = (q * u * q⁻¹) * (u * b) := by rw [hqb]
  have hvu : (q * u * q⁻¹) * u = 1 := by
    have h1 : (1 : G) * b = ((q * u * q⁻¹) * u) * b := by
      rw [one_mul, mul_assoc]
      exact hb_eq
    exact mul_right_cancel h1.symm
  have hqu : q * u * q⁻¹ = u :=
    (eq_inv_of_mul_eq_one_left hvu).trans (inv_eq_of_mul_eq_one_right hu2)
  rcases CV_q hc.toCtx4Q huV hqu with hu1 | huz
  · left
    have hqb' : q * b * q⁻¹ = b := by
      have h := hqb
      rw [hu1, one_mul] at h
      exact h
    have hqa : q * a * q⁻¹ = a := by
      rw [ha_eq]
      have hsq : s * q⁻¹ = q⁻¹ * s := by rw [hqinv]; exact hqs.symm
      calc q * (b * s) * q⁻¹
          = q * b * (s * q⁻¹) := by group
        _ = q * b * (q⁻¹ * s) := by rw [hsq]
        _ = (q * b * q⁻¹) * s := by group
        _ = b * s := by rw [hqb']
    calc q * a = q * a * q⁻¹ * q := by group
      _ = a * q := by rw [hqa]
  · right
    have hqa : q * a * q⁻¹ = (x₁ * x₂) ^ 2 * a := by
      have h := hcomm
      rw [huz] at h
      exact (mul_inv_eq_iff_eq_mul).mp h
    have hqcomm' : q * (a * x₁ ^ 2) * q⁻¹ = a * x₁ ^ 2 := by
      calc q * (a * x₁ ^ 2) * q⁻¹
          = (q * a * q⁻¹) * (q * x₁ ^ 2 * q⁻¹) := by group
        _ = ((x₁ * x₂) ^ 2 * a) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) := by rw [hqa, hqy]
        _ = a * x₁ ^ 2 := by
              have hza : (x₁ * x₂) ^ 2 * a = a * (x₁ * x₂) ^ 2 :=
                (V_comm_O hc ha (subset_closure (by simp))).symm
              have hzy : (x₁ * x₂) ^ 2 * x₁ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 :=
                (y_comm_z hc.toCtx4Q).symm
              rw [hza]
              calc (a * (x₁ * x₂) ^ 2) * (x₁ ^ 2 * (x₁ * x₂) ^ 2)
                  = a * ((x₁ * x₂) ^ 2 * x₁ ^ 2) * (x₁ * x₂) ^ 2 := by group
                _ = a * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by rw [hzy]
                _ = a * x₁ ^ 2 * ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2) := by group
                _ = a * x₁ ^ 2 := by rw [z_mul_self hc.toCtx4Q, mul_one]
    calc q * (a * x₁ ^ 2) = q * (a * x₁ ^ 2) * q⁻¹ * q := by group
      _ = (a * x₁ ^ 2) * q := by rw [hqcomm']

theorem card_CO_q_le :
    Nat.card (ctxO t tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G) : Subgroup G) ≤ 32 := by
  let C₁ : Subgroup G := ctxO t tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G)
  let C₂ : Subgroup G := ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)
  have hle : C₁ ≤ C₂ := inf_le_inf_right _ (O_le_U hc)
  have hcard₂ : Nat.card C₂ = 64 := by
    change Nat.card (ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) : Subgroup G) = 64
    rw [hc.card_CU_tl]
    norm_num
  have hqC2 : t * lam ∈ C₂ := by
    refine ⟨q_mem_U hc, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hq_not_C1 : t * lam ∉ C₁ := fun h => q_not_mem_O hc h.1
  have hdiv : Nat.card C₁ ∣ 64 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hcard₂] at h
  have hne : Nat.card C₁ ≠ 64 := by
    intro h64
    have heq : C₁ = C₂ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard₂, h64])
    exact hq_not_C1 (heq.symm ▸ hqC2)
  change Nat.card C₁ ≤ 32
  rcases hdiv with ⟨k, hk⟩
  have hk1 : k ≠ 1 := by
    intro hk1
    exact hne (by rw [hk1, mul_one] at hk; exact hk.symm)
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    exact absurd hk (by norm_num)
  have hk2 : 2 ≤ k := by omega
  have h2n : 2 * Nat.card C₁ ≤ 64 := by
    calc 2 * Nat.card C₁ ≤ k * Nat.card C₁ := Nat.mul_le_mul_right _ hk2
      _ = Nat.card C₁ * k := by rw [mul_comm]
      _ = 64 := hk.symm
  omega

theorem card_fix_le :
    Nat.card {a : G // a ∈ ctxO t tau x₁ x₂ ∧
      (t * lam) * a * (t * lam)⁻¹ * a⁻¹ ∈ ctxX t tau x₁ x₂} ≤ 64 := by
  let S₁ : Set G := {a : G | a ∈ ctxO t tau x₁ x₂ ∧
      (t * lam) * a * (t * lam)⁻¹ * a⁻¹ ∈ ctxX t tau x₁ x₂}
  let C₁ : Subgroup G := ctxO t tau x₁ x₂ ⊓ centralizer ({t * lam} : Set G)
  have hcard : Nat.card {a : G // a ∈ ctxO t tau x₁ x₂ ∧
      (t * lam) * a * (t * lam)⁻¹ * a⁻¹ ∈ ctxX t tau x₁ x₂} = S₁.ncard := rfl
  rw [hcard]
  have hC1 : (C₁ : Set G).ncard ≤ 32 := by
    rw [← Nat.card_coe_set_eq]
    exact card_CO_q_le hc
  have hsub : S₁ ⊆ (C₁ : Set G) ∪ (fun c : G => c * x₁ ^ 2) '' (C₁ : Set G) := by
    intro a ha
    rcases fix_cases hc ha.1 ha.2 with hca | hcay
    · left
      refine ⟨ha.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hca
    · right
      rw [Set.mem_image]
      refine ⟨a * x₁ ^ 2, ⟨?_, ?_⟩, ?_⟩
      · exact mul_mem ha.1 (hc.toCtx4Q.Q_le_O (hc.toCtx4Q.V_le_Q (subset_closure (by simp))))
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hcay
      · rw [mul_assoc, y_mul_self hc.toCtx4Q, mul_one]
  calc S₁.ncard ≤ ((C₁ : Set G) ∪ (fun c : G => c * x₁ ^ 2) '' (C₁ : Set G)).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (C₁ : Set G).ncard + ((fun c : G => c * x₁ ^ 2) '' (C₁ : Set G)).ncard :=
        Set.ncard_union_le _ _
    _ = (C₁ : Set G).ncard + (C₁ : Set G).ncard := by
        rw [Set.ncard_image_of_injective (C₁ : Set G) (mul_left_injective (x₁ ^ 2))]
    _ ≤ 32 + 32 := add_le_add hC1 hC1
    _ = 64 := by norm_num

end Fix

end CFSG.OddStandard.SmallF3.HarrisU33.L34
