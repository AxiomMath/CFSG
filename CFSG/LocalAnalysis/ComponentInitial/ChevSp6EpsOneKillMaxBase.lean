
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillAction

@[expose] public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

theorem om2T_order : compT (compT omT omT) (compT (compT omT omT) (compT omT omT)) = idT := by
  decide +kernel

theorem wl_zero : wpart 0 = 0 := rfl

theorem wl_xor : ∀ v w, v < 64 → w < 64 → wpart v = 0 → wpart w = 0 → wpart (v ^^^ w) = 0 :=
  fun v w hv hw h1 h2 => by rw [wpart_xor v hv w hw, h1, h2]; rfl

theorem wr_zero : wpart 0 = xpart 0 := rfl

theorem wr_xor : ∀ v w, v < 64 → w < 64 → wpart v = xpart v → wpart w = xpart w →
    wpart (v ^^^ w) = xpart (v ^^^ w) :=
  fun v w hv hw h1 h2 => by rw [wpart_xor v hv w hw, xpart_xor v hv w hw, h1, h2]

theorem card_nl : Nat.card {v : Fin 64 // wpart v = 0} = 8 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem card_nr : Nat.card {v : Fin 64 // wpart v = xpart v} = 8 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem eq_one_of_cube {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) {k : ℕ}
    (hk : σ ^ 2 ^ k = 1) (h3 : compT (tupleOf σ) (compT (tupleOf σ) (tupleOf σ)) = idT) :
    σ = 1 := by
  have hc : σ ^ 3 = 1 := by
    apply tupleOf_injective (pow_mem hσ 3).1 (one_mem (Gq u)).1
    rw [tupleOf_one, pow_three, tupleOf_mul hσ.1, tupleOf_mul hσ.1, h3]
  have h1 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hc
  have h2 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h3' : orderOf σ ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
  have hg : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3'
  exact h3'

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)

def preim (p : ℕ → Prop) (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w)) : Subgroup G where
  carrier := {x | x ∈ Jh ∧ p (cV x)}
  mul_mem' := by
    rintro x y ⟨hx, hpx'⟩ ⟨hy, hpy⟩
    refine ⟨mul_mem hx hy, ?_⟩
    rw [h.cV_mul x hx y hy]
    exact hpx _ _ (h.cV_lt x hx) (h.cV_lt y hy) hpx' hpy
  one_mem' := ⟨one_mem _, by rw [h.cV_one]; exact hp0⟩
  inv_mem' := by
    rintro x ⟨hx, hpx'⟩
    exact ⟨inv_mem hx, by rw [h.cV_inv hx]; exact hpx'⟩

def Jl : Subgroup G := h.preim (fun v => wpart v = 0) wl_zero wl_xor

def Jr : Subgroup G := h.preim (fun v => wpart v = xpart v) wr_zero wr_xor

include h

theorem preim_le {p : ℕ → Prop} (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w)) : h.preim p hp0 hpx ≤ Jh :=
  fun _ hx => hx.1

theorem E_le_preim {p : ℕ → Prop} (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w)) : E ≤ h.preim p hp0 hpx :=
  fun e he => ⟨h.E_le he, by rw [(h.cV_eq_zero e (h.E_le he)).2 he]; exact hp0⟩

theorem card_preim {p : ℕ → Prop} (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w)) :
    Nat.card (h.preim p hp0 hpx) = Nat.card {v : Fin 64 // p v} * 512 := by
  rw [h.card_of_le (h.E_le_preim hp0 hpx) (h.preim_le hp0 hpx)]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun ⟨x, hx, hxv⟩ => hxv ▸ hx.2,
    fun hv => ?_⟩)
  obtain ⟨x, hx, hxv⟩ := h.cV_surj v v.2
  exact ⟨x, ⟨hx, hxv ▸ hv⟩, hxv⟩

theorem preim_ea {p : ℕ → Prop} (hp0 : p 0)
    (hpx : ∀ v w, v < 64 → w < 64 → p v → p w → p (v ^^^ w))
    (hps : ∀ v, v < 64 → p v → qOf u v = 0) :
    (∀ a ∈ h.preim p hp0 hpx, ∀ b ∈ h.preim p hp0 hpx, a * b = b * a) ∧
      ∀ a ∈ h.preim p hp0 hpx, a * a = 1 := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have hc := h.cE_comm ha.1 hb.1
    have hav := h.cV_lt a ha.1
    have hbv := h.cV_lt b hb.1
    have hβ : betaOf u (cV a) (cV b) = 0 := by
      unfold betaOf
      rw [hps _ (Nat.xor_lt_two_pow (n := 6) hav hbv) (hpx _ _ hav hbv ha.2 hb.2),
        hps _ hav ha.2, hps _ hbv hb.2]
      rfl
    rw [hβ] at hc
    have h1 := h.cE_inj _ (h.comm_mem_E ha.1 hb.1) hc
    calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [h1, mul_one]
  · exact h.cE_inj _ (h.sq a ha.1).1 (by rw [(h.sq a ha.1).2, hps _ (h.cV_lt a ha.1) ha.2])

theorem Jl_le : h.Jl ≤ Jh := h.preim_le (p := fun v => wpart v = 0) wl_zero wl_xor

theorem Jr_le : h.Jr ≤ Jh := h.preim_le (p := fun v => wpart v = xpart v) wr_zero wr_xor

theorem E_le_Jl : E ≤ h.Jl := h.E_le_preim (p := fun v => wpart v = 0) wl_zero wl_xor

theorem card_Jl : Nat.card h.Jl = 2 ^ 12 := by
  rw [Jl, h.card_preim (p := fun v => wpart v = 0), card_nl]; norm_num

theorem card_Jr : Nat.card h.Jr = 2 ^ 12 := by
  rw [Jr, h.card_preim (p := fun v => wpart v = xpart v), card_nr]; norm_num

theorem Jl_ea (hu : u = false) :
    (∀ a ∈ h.Jl, ∀ b ∈ h.Jl, a * b = b * a) ∧ ∀ a ∈ h.Jl, a * a = 1 := by
  subst hu
  exact h.preim_ea (p := fun v => wpart v = 0) wl_zero wl_xor fun v hv hw => nl_sing v hv hw

theorem Jr_ea (hu : u = false) :
    (∀ a ∈ h.Jr, ∀ b ∈ h.Jr, a * b = b * a) ∧ ∀ a ∈ h.Jr, a * a = 1 := by
  subst hu
  exact h.preim_ea (p := fun v => wpart v = xpart v) wr_zero wr_xor fun v hv hw => nr_sing v hv hw

theorem Jh_le_sup : Jh ≤ h.Jl ⊔ h.Jr := by
  intro x hx
  obtain ⟨a, ha, hwa, hwb⟩ := nl_nr_span (cV x) (h.cV_lt x hx)
  have hb : a ^^^ cV x < 64 := Nat.xor_lt_two_pow (n := 6) ha (h.cV_lt x hx)
  have hxa : h.liftV a ∈ h.Jl := ⟨h.liftV_mem a, by rw [h.cV_liftV ha]; exact hwa⟩
  have hxb : h.liftV (a ^^^ cV x) ∈ h.Jr := ⟨h.liftV_mem _, by rw [h.cV_liftV hb]; exact hwb⟩
  have hab := mul_mem (h.liftV_mem a) (h.liftV_mem (a ^^^ cV x))
  have he : (h.liftV a * h.liftV (a ^^^ cV x))⁻¹ * x ∈ E :=
    h.mem_E_of_cV_eq hab hx (by
      rw [h.cV_mul _ (h.liftV_mem a) _ (h.liftV_mem _), h.cV_liftV ha, h.cV_liftV hb,
        ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor])
  have e : x = h.liftV a * h.liftV (a ^^^ cV x) *
      ((h.liftV a * h.liftV (a ^^^ cV x))⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mul_mem (mem_sup_left hxa) (mem_sup_right hxb)) (mem_sup_left (h.E_le_Jl he))

variable [Finite G]

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
