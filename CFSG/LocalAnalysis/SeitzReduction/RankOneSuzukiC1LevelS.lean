module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1LevelBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem comm_t_mem (h : SzC1Stage G L f a t T d V U U₁ k) {x : G} (hx : x ∈ U) :
    x * t * x⁻¹ * t⁻¹ ∈ V := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  have hK' : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, h.hfa]
  set z := x * t * x⁻¹ with hz
  have hzR : z ∈ szR (szT₁ L T) V t :=
    (mem_normalizer_iff.mp (h.U_le hx) t).mp (mem_szR_right _ V t)
  have hzU₁ : z ∉ U₁ := fun hz1 => h.t_not_mem (by
    have := h.conj_mem_U₁ (inv_mem hx) hz1
    rwa [hz, show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at this)
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
    h.t_mem_normalizer_sup hzR with h1 | h1
  · exact absurd (h.sup_le_U₁ h1) hzU₁
  · obtain ⟨y, hy, r, hr, hyr⟩ := h.exists_mul_of_mem_sup h1
    have hzt : z = y * r * t := by
      rw [← hyr, mul_assoc, h.t_mul_self, mul_one]
    have hsq : z ^ 2 = 1 := by
      rw [hz, sq, show x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, h.t_mul_self,
        mul_one, mul_inv_cancel]
    rw [hzt, h.sq_mul_mul_t hy hr] at hsq
    have hyA := SzC1.mem_szA₁_of_sq_eq_one hc h.ha hK' hy hsq
    rw [h.t_inv, hyr]
    exact mul_mem (h.le hyA) hr

theorem mem_szR_of_comm_t_mem (h : SzC1Stage G L f a t T d V U U₁ k) {x : G} (hx : x ∈ U)
    (hσ : x * t * x⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T)) : x ∈ szR (szT₁ L T) V t := by
  by_contra hR
  refine h.conj_t_not_mem x hx hR ?_
  rw [show x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t by group]
  exact mul_mem (szA₁_le_szA L T t hσ) (mem_szA_right L T t)

theorem comm_t_of_mem_sup (h : SzC1Stage G L f a t T d V U U₁ k) {y r : G}
    (hy : y ∈ szT₁ L T) (hr : r ∈ V) : y * r * t * (y * r)⁻¹ * t⁻¹ = r ^ 2 := by
  rw [SzC1.comm_t_mul, h.comm_t_of_mem_V hr, h.comm_t_of_mem_T₁ hy, mul_one,
    mem_centralizer_iff.mp (h.le_centralizer (pow_mem hr 2)) y hy, mul_inv_cancel_right]

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}
  (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem card_K : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, h.hfa]

theorem card_szA₁ : Nat.card (szA₁ (szT₁ L T)) = 2 ^ f := by
  rw [hc.card_szA₁ h.ha (h.card_K hK hc), Nat.card_eq_fintype_card, hK]

theorem card_T₁ : Nat.card (szT₁ L T) = (2 ^ f) ^ 2 := by
  rw [hc.card_eq, Nat.card_eq_fintype_card, hK, sq]

theorem relIndex_V_sup : V.relIndex (szT₁ L T ⊔ V) = 2 ^ f := by
  rw [SzC1.relIndex_sup_eq_relIndex_inf h.T₁_le_normalizer_V, h.inf_eq_szA₁]
  have h1 := relIndex_mul_card (H := szA₁ (szT₁ L T)) (K := szT₁ L T)
  rw [inf_of_le_left (szA₁_le _), h.card_szA₁ hK hc, h.card_T₁ hK hc, sq] at h1
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h1

theorem card_sup : Nat.card (szT₁ L T ⊔ V : Subgroup G) = (2 ^ f) ^ (k + 2) := by
  have h1 := relIndex_mul_card (H := V) (K := szT₁ L T ⊔ V)
  rw [inf_of_le_left le_sup_right, h.relIndex_V_sup hK hc, h.card] at h1
  rw [← h1]
  ring

theorem one_lt_q : 1 < 2 ^ f := Nat.one_lt_two_pow (by rw [h.hfa]; omega)

theorem card_sup_lt : Nat.card (szT₁ L T ⊔ V : Subgroup G) < Nat.card U₁ := by
  rw [h.card_sup hK hc, h.card_U₁]
  exact Nat.pow_lt_pow_right (h.one_lt_q hK hc) (by omega)

theorem one_le_k : 1 ≤ k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst hk0
  have hVA : szA₁ (szT₁ L T) = V := Subgroup.eq_of_le_of_card_ge h.le (by
    rw [h.card, h.card_szA₁ hK hc, zero_add, pow_one])
  have hle : U₁ ≤ szT₁ L T ⊔ V := fun x hx => by
    rw [← h.inf_eq]
    have hσ := h.comm_t_mem (h.U₁_le hx)
    rw [← hVA] at hσ
    exact mem_inf.mpr ⟨hx, h.mem_szR_of_comm_t_mem (h.U₁_le hx) hσ⟩
  exact absurd (Subgroup.card_le_of_le hle) (not_le.mpr (h.card_sup_lt hK hc))

theorem S_mul {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₁) :
    v ((x * y * t * (x * y)⁻¹ * t⁻¹) ^ 2 ^ k) =
      v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) + v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k) := by
  have hσy := h.comm_t_mem (h.U₁_le hy)
  have hσx := h.comm_t_mem (h.U₁_le hx)
  rw [SzC1.comm_t_mul, (Commute.mul_pow (h.comm _ (h.conj_V hx hσy) _ hσx) _), conj_pow,
    h.conj_szA₁ x (h.U₁_le hx) _ (h.pow_mem_szA₁ hσy),
    hc.v_mul_szA₁ h.ha (h.card_K hK hc) (h.pow_mem_szA₁ hσy) (h.pow_mem_szA₁ hσx), add_comm]

theorem S_conj_d {x : G} (hx : x ∈ U₁) :
    v ((d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹) ^ 2 ^ k) =
      κ ^ (2 ^ (a + 1) + 1) * v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) := by
  have hdt : d * t = t * d := (mem_centralizer_singleton_iff.mp h.d_norm.2)
  have e1 : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
  have e2 : d * t⁻¹ * d⁻¹ = t⁻¹ := by rw [h.t_inv, e1]
  have e : d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹ =
      d⁻¹ * (x * (d * t * d⁻¹) * x⁻¹ * (d * t⁻¹ * d⁻¹)) * d⁻¹⁻¹ := by group
  rw [e1, e2] at e
  rw [e, conj_pow, inv_inv, hc.v_conj_szA₁ h.ha (h.card_K hK hc)
    (h.pow_mem_szA₁ (h.comm_t_mem (h.U₁_le hx)))]

theorem S_eq_zero_of_mem_sup {x : G} (hx : x ∈ szT₁ L T ⊔ V) :
    v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = 0 := by
  obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hx
  rw [h.comm_t_of_mem_sup hy hr, ← pow_mul, ← pow_succ', h.pow r hr, hc.v_one]

theorem mem_sup_of_S_eq_zero {x : G} (hx : x ∈ U₁) (h0 : v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = 0) :
    x ∈ szT₁ L T ⊔ V := by
  have hσ := h.comm_t_mem (h.U₁_le hx)
  have h1 : (x * t * x⁻¹ * t⁻¹) ^ 2 ^ k = 1 :=
    hc.eq_one_of_v_eq_zero h.ha (h.card_K hK hc) (h.pow_mem_szA₁ hσ) h0
  obtain ⟨w, hw, hxw⟩ := SzC1.exists_sq_eq_of_pow_eq_one h.comm h.omega h.pow
    (by rw [h.card_szA₁ hK hc, h.card]) hσ h1
  have hwx : w⁻¹ * x ∈ szT₁ L T := by
    refine h.mem_T₁_of_comm (mul_mem (inv_mem (h.V_le_U₁ hw)) hx) ?_
    have e1 : x * t * x⁻¹ = w * t * w⁻¹ := by
      rw [show x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t by group, hxw, ← h.comm_t_of_mem_V hw]
      group
    calc w⁻¹ * x * t = w⁻¹ * (x * t * x⁻¹) * x := by group
      _ = w⁻¹ * (w * t * w⁻¹) * x := by rw [e1]
      _ = t * (w⁻¹ * x) := by group
  have hmem : w * (w⁻¹ * x) ∈ szT₁ L T ⊔ V := mul_mem (mem_sup_right hw) (mem_sup_left hwx)
  rwa [mul_inv_cancel_left] at hmem

theorem exists_S_ne_zero : ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hle : U₁ ≤ szT₁ L T ⊔ V := fun x hx => h.mem_sup_of_S_eq_zero hK hc hx (hne x hx)
  exact absurd (Subgroup.card_le_of_le hle) (not_le.mpr (h.card_sup_lt hK hc))

theorem S_surj (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (s : K) :
    ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = s := by
  by_cases hs : s = 0
  · exact ⟨1, one_mem _, by simp [hs, hc.v_one]⟩
  obtain ⟨x₀, hx₀, hS₀⟩ := h.exists_S_ne_zero hK hc
  have hcardK : Nat.card K = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card, h.card_K hK hc]
  have hμ := pow_theta_succ_generator_of_generator h.ha hcardK hκ
  obtain ⟨m, hm⟩ := hμ (s / v ((x₀ * t * x₀⁻¹ * t⁻¹) ^ 2 ^ k)) (div_ne_zero hs hS₀)
  have key : ∀ n : ℕ, ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) =
      (κ ^ (2 ^ (a + 1) + 1)) ^ n * v ((x₀ * t * x₀⁻¹ * t⁻¹) ^ 2 ^ k) := by
    intro n
    induction n with
    | zero => exact ⟨x₀, hx₀, by rw [pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨x, hx, hxS⟩ := ih
      refine ⟨d⁻¹ * x * d, by simpa using (mem_normalizer_iff.mp (inv_mem h.d_mem_U₁) x).mp hx, ?_⟩
      rw [h.S_conj_d hK hc hx, hxS, pow_succ]
      ring
  obtain ⟨x, hx, hxS⟩ := key m
  exact ⟨x, hx, by rw [hxS, hm, div_mul_cancel₀ s hS₀]⟩

theorem exists_comm_t_eq (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) {r : G} (hr : r ∈ V) :
    ∃ y ∈ U₁, y * t * y⁻¹ * t⁻¹ = r := by
  have hK' := h.card_K hK hc
  obtain ⟨y₀, hy₀, hS⟩ := h.S_surj hK hc hκ (v (r ^ 2 ^ k))
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ = y₀ * t * y₀⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hσ : σ₀ ∈ V := hσ₀ ▸ h.comm_t_mem (h.U₁_le hy₀)
  rw [← hσ₀] at hS
  have heq : σ₀ ^ 2 ^ k = r ^ 2 ^ k :=
    hc.inj _ (szA₁_le _ (h.pow_mem_szA₁ hσ)) _ (szA₁_le _ (h.pow_mem_szA₁ hr))
      (by rw [hc.u_eq_zero_of_mem_szA₁ h.ha hK' (h.pow_mem_szA₁ hσ),
        hc.u_eq_zero_of_mem_szA₁ h.ha hK' (h.pow_mem_szA₁ hr)]) hS
  have h1 : (σ₀⁻¹ * r) ^ 2 ^ k = 1 := by
    rw [(Commute.mul_pow (h.comm _ (inv_mem hσ) _ hr) _), inv_pow, heq, inv_mul_cancel]
  obtain ⟨w, hw, hw2⟩ := SzC1.exists_sq_eq_of_pow_eq_one h.comm h.omega h.pow
    (by rw [h.card_szA₁ hK hc, h.card]) (mul_mem (inv_mem hσ) hr) h1
  refine ⟨w * y₀, mul_mem (h.V_le_U₁ hw) hy₀, ?_⟩
  have hc1 : w * σ₀ * w⁻¹ = σ₀ := by rw [h.comm w hw σ₀ hσ, mul_inv_cancel_right]
  rw [SzC1.comm_t_mul, ← hσ₀, h.comm_t_of_mem_V hw, hc1, ← hw2]
  group

end Coords

end SzC1Stage

end CFSG.SeitzReduction.RankOne
