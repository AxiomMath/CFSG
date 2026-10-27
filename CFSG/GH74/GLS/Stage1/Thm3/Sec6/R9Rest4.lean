module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q : Subgroup G} {FA : G → Prop}

namespace Setup9

variable {U : Subgroup G} {x u₁ u₂ : G} (c : Setup9 G z S P Q FA U x u₁ u₂)
include c


theorem card_V₂ : Nat.card ↥(Q ⊓ centralizer ({u₂} : Set G)) =
    Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := by
  have h1 := Subgroup.relIndex_mul_card (Q ⊓ centralizer ({u₂} : Set G)) Q
  rw [c.V₂_idx, inf_of_le_left inf_le_left] at h1
  have h2 := c.card_P_eq
  have h3 := c.card_eq
  omega

theorem z'_conj_q {q : G} (hq : q ∈ Q) (hqV : q ∉ Q ⊓ centralizer ({u₂} : Set G)) :
    (x * z * x⁻¹) * q * (x * z * x⁻¹)⁻¹ = z * q := by
  obtain ⟨-, hqinv⟩ := c.quatOut₂ q hq hqV
  have h1 : q * u₂⁻¹ * q⁻¹ = u₂ := by
    have := hqinv u₂ c.u₂_mem_V₂
    calc q * u₂⁻¹ * q⁻¹ = (q * u₂ * q⁻¹)⁻¹ := by group
      _ = (u₂⁻¹)⁻¹ := by rw [this]
      _ = u₂ := inv_inv u₂
  have hu₁q : u₁ * (u₂ * q * u₂⁻¹) = (u₂ * q * u₂⁻¹) * u₁ :=
    c.cfg.PQ_comm u₁ c.u₁_mem _ (Q.mul_mem (Q.mul_mem c.u₂_mem hq) (Q.inv_mem c.u₂_mem))
  have hkey : (u₁ * u₂) * q * (u₁ * u₂)⁻¹ = z * q := by
    calc (u₁ * u₂) * q * (u₁ * u₂)⁻¹ = u₁ * (u₂ * q * u₂⁻¹) * u₁⁻¹ := by group
      _ = (u₂ * q * u₂⁻¹) * u₁ * u₁⁻¹ := by rw [hu₁q]
      _ = u₂ * q * u₂⁻¹ := by group
      _ = u₂ * (q * u₂⁻¹ * q⁻¹) * q := by group
      _ = u₂ * u₂ * q := by rw [h1]
      _ = z * q := by rw [c.u₂_sq]
  have hzs : ∀ s ∈ S, z * s * z⁻¹ = s := fun s hs => by
    have := c.z_comm hs
    rw [← this]; group
  rcases c.z'_cases with e | e
  · rw [e]; exact hkey
  · rw [e]
    have hmemS : (u₁ * u₂) * q * (u₁ * u₂)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (c.U_le_S c.u_mem) (c.cfg.Q_le hq)) (S.inv_mem (c.U_le_S c.u_mem))
    calc (z * (u₁ * u₂)) * q * (z * (u₁ * u₂))⁻¹ = z * ((u₁ * u₂) * q * (u₁ * u₂)⁻¹) * z⁻¹ := by
          group
      _ = (u₁ * u₂) * q * (u₁ * u₂)⁻¹ := hzs _ hmemS
      _ = z * q := hkey

structure Gd (c : Setup9 G z S P Q FA U x u₁ u₂) (a₀ p₀ q₀ : G) : Prop where
  a_mem : a₀ ∈ P ⊓ centralizer ({u₁} : Set G)
  gen : ∀ v ∈ P ⊓ centralizer ({u₁} : Set G), v ∈ zpowers a₀
  p_mem : p₀ ∈ P
  q_mem : q₀ ∈ Q
  p_not : p₀ ∉ P ⊓ centralizer ({u₁} : Set G)
  q_not : q₀ ∉ Q ⊓ centralizer ({u₂} : Set G)

namespace Gd

variable {c} {a₀ p₀ q₀ : G} (d : Gd c a₀ p₀ q₀)
include d

theorem u'_sq' : (p₀ * q₀) * (p₀ * q₀) = 1 := c.u'_sq d.p_mem d.q_mem d.p_not d.q_not

theorem u'_inv_eq : (p₀ * q₀)⁻¹ = p₀ * q₀ := inv_eq_of_mul_eq_one_right d.u'_sq'

theorem u'_W : p₀ * q₀ ∈ S ⊓ centralizer (U : Set G) :=
  c.u'_mem_W d.p_mem d.q_mem d.p_not d.q_not

theorem u'_notin_A : p₀ * q₀ ∉ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹) := by
  intro hmem
  have h1 := c.A_comm_V d.a_mem d.gen hmem c.u₁_mem_V₁
  have h2 := c.u'_inv₁ d.p_mem d.q_mem d.p_not u₁ c.u₁_mem_V₁
  have h3 : u₁ = u₁⁻¹ := by
    rw [← h2, h1]; group
  have h4 : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = u₁ * u₁⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel u₁
  exact c.hz1 (by rw [← c.u₁_sq]; exact h4)

theorem A_norm_u' : ∀ a ∈ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹),
    (p₀ * q₀) * a * (p₀ * q₀)⁻¹ ∈ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹) := by
  intro a ha
  obtain ⟨v, hv, t, ht, rfl⟩ := c.A_mem d.a_mem d.gen ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  obtain ⟨k', hk'⟩ := c.W_norm_g d.a_mem d.gen d.u'_W k
  have h1 := c.u'_inv₁ d.p_mem d.q_mem d.p_not v hv
  have : (p₀ * q₀) * (v * (x * a₀ * x⁻¹) ^ k) * (p₀ * q₀)⁻¹ = v⁻¹ * (x * a₀ * x⁻¹) ^ k' := by
    calc (p₀ * q₀) * (v * (x * a₀ * x⁻¹) ^ k) * (p₀ * q₀)⁻¹
        = ((p₀ * q₀) * v * (p₀ * q₀)⁻¹) * ((p₀ * q₀) * (x * a₀ * x⁻¹) ^ k * (p₀ * q₀)⁻¹) := by
          group
      _ = v⁻¹ * (x * a₀ * x⁻¹) ^ k' := by rw [h1, hk']
  rw [this]
  exact mul_mem (mem_sup_left (inv_mem hv)) (mem_sup_right (Subgroup.mem_zpowers_iff.2 ⟨k', rfl⟩))

theorem u'_normalizes_A : zpowers (p₀ * q₀) ≤
    normalizer (((P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹) : Subgroup G) : Set G) := by
  refine zpowers_le.2 (mem_normalizer_of_both d.A_norm_u' (fun a ha => ?_))
  rw [d.u'_inv_eq]
  have := d.A_norm_u' a ha
  rwa [d.u'_inv_eq] at this

theorem W_eq : S ⊓ centralizer (U : Set G) =
    ((P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹)) ⊔ zpowers (p₀ * q₀) := by
  have hBW : ((P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹)) ⊔ zpowers (p₀ * q₀) ≤
      S ⊓ centralizer (U : Set G) :=
    sup_le (sup_le c.V₁_le_W (zpowers_le.2 (c.g_mem_W d.a_mem))) (zpowers_le.2 d.u'_W)
  refine (Subgroup.eq_of_le_of_card_ge hBW ?_).symm
  have hA := c.A_card d.a_mem d.gen
  have hinf : ((P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹)) ⊓ zpowers (p₀ * q₀) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rcases (mem_zpowers_of_sq d.u'_sq').1 ha.2 with h | h
    · rw [h]; exact one_mem _
    · exact absurd (h ▸ ha.1) d.u'_notin_A
  have hcardu : Nat.card ↥(zpowers (p₀ * q₀)) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_two_of_sq_one d.u'_sq' ?_
    intro h
    have := d.u'_notin_A
    apply this
    rw [h]; exact one_mem _
  have hB := card_sup_mul_card_inf d.u'_normalizes_A
  rw [hinf, Subgroup.card_bot, mul_one, hcardu, hA] at hB
  have hW := c.W_card_le
  have hS := c.card_S
  have hR := c.card_R
  have hP := c.card_P_eq
  have hPQ := c.card_eq
  rw [hB]
  nlinarith


theorem W_cases {w : G} (hw : w ∈ S ⊓ centralizer (U : Set G)) :
    w ∈ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹) ∨
      w * (p₀ * q₀)⁻¹ ∈ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹) := by
  rw [d.W_eq, sup_comm] at hw
  obtain ⟨t, ht, a, ha, rfl⟩ := mem_sup_of_le_normalizer d.u'_normalizes_A hw
  rcases (mem_zpowers_of_sq d.u'_sq').1 ht with h1 | h1
  · left; rw [h1, one_mul]; exact ha
  · right; rw [h1]; exact d.A_norm_u' a ha

theorem u'_inv_g : (p₀ * q₀) * (x * a₀ * x⁻¹) * (p₀ * q₀)⁻¹ = (x * a₀ * x⁻¹)⁻¹ := by
  have hu'a := c.u'_inv₁ d.p_mem d.q_mem d.p_not a₀ d.a_mem
  have hccW : x⁻¹ * (p₀ * q₀) * x ∈ S ⊓ centralizer (U : Set G) := c.xinv_W d.u'_W
  have hccA : x⁻¹ * (p₀ * q₀) * x ∉ (P ⊓ centralizer ({u₁} : Set G)) ⊔ zpowers (x * a₀ * x⁻¹) := by
    intro hA
    have h0 := c.A_comm_V d.a_mem d.gen hA d.a_mem
    have hu'g : (p₀ * q₀) * (x * a₀ * x⁻¹) = (x * a₀ * x⁻¹) * (p₀ * q₀) := by
      have : x * ((x⁻¹ * (p₀ * q₀) * x) * a₀) * x⁻¹ = x * (a₀ * (x⁻¹ * (p₀ * q₀) * x)) * x⁻¹ := by
        rw [h0]
      calc (p₀ * q₀) * (x * a₀ * x⁻¹) = x * ((x⁻¹ * (p₀ * q₀) * x) * a₀) * x⁻¹ := by group
        _ = x * (a₀ * (x⁻¹ * (p₀ * q₀) * x)) * x⁻¹ := this
        _ = (x * a₀ * x⁻¹) * (p₀ * q₀) := by group
    have hWg : ∀ w ∈ S ⊓ centralizer (U : Set G), w * (x * a₀ * x⁻¹) = (x * a₀ * x⁻¹) * w := by
      intro w hw
      rcases d.W_cases hw with h | h
      · exact c.A_comm_g d.a_mem d.gen h
      · have hα := c.A_comm_g d.a_mem d.gen h
        generalize x * a₀ * x⁻¹ = g at hu'g hα ⊢
        generalize p₀ * q₀ = u' at hu'g hα ⊢
        calc w * g = (w * u'⁻¹) * (u' * g) := by group
          _ = (w * u'⁻¹) * (g * u') := by rw [hu'g]
          _ = ((w * u'⁻¹) * g) * u' := by group
          _ = (g * (w * u'⁻¹)) * u' := by rw [hα]
          _ = g * w := by group
    have hxu : x * (p₀ * q₀) * x⁻¹ ∈ S ⊓ centralizer (U : Set G) := (c.x_W (p₀ * q₀)).1 d.u'_W
    have h1 := hWg _ hxu
    have h2 : (p₀ * q₀) * a₀ = a₀ * (p₀ * q₀) := by
      have h3 : x * ((p₀ * q₀) * a₀) * x⁻¹ = x * (a₀ * (p₀ * q₀)) * x⁻¹ := by
        calc x * ((p₀ * q₀) * a₀) * x⁻¹ = (x * (p₀ * q₀) * x⁻¹) * (x * a₀ * x⁻¹) := by group
          _ = (x * a₀ * x⁻¹) * (x * (p₀ * q₀) * x⁻¹) := h1
          _ = x * (a₀ * (p₀ * q₀)) * x⁻¹ := by group
      have h4 := mul_left_cancel (mul_right_cancel h3)
      exact h4
    have h5 : a₀ = a₀⁻¹ := by rw [← hu'a, h2]; group
    have h6 : a₀ * a₀ = 1 := by
      calc a₀ * a₀ = a₀ * a₀⁻¹ := by rw [← h5]
        _ = 1 := mul_inv_cancel a₀
    rcases (mem_zpowers_of_sq h6).1 (d.gen u₁ c.u₁_mem_V₁) with h7 | h7
    · exact c.u₁_ne.1 h7
    · apply c.hz1
      rw [← c.u₁_sq, h7]; exact h6
  have hα := (d.W_cases hccW).resolve_left hccA
  have hαa := c.A_comm_V d.a_mem d.gen hα d.a_mem
  have hcc : (x⁻¹ * (p₀ * q₀) * x) * a₀ * (x⁻¹ * (p₀ * q₀) * x)⁻¹ = a₀⁻¹ := by
    generalize hα' : (x⁻¹ * (p₀ * q₀) * x) * (p₀ * q₀)⁻¹ = α at hαa
    have e : x⁻¹ * (p₀ * q₀) * x = α * (p₀ * q₀) := by rw [← hα']; group
    rw [e]
    calc α * (p₀ * q₀) * a₀ * (α * (p₀ * q₀))⁻¹ = α * ((p₀ * q₀) * a₀ * (p₀ * q₀)⁻¹) * α⁻¹ := by group
      _ = α * a₀⁻¹ * α⁻¹ := by rw [hu'a]
      _ = a₀⁻¹ := by
        calc α * a₀⁻¹ * α⁻¹ = (α * a₀ * α⁻¹)⁻¹ := by group
          _ = a₀⁻¹ := by rw [hαa]; group
  calc (p₀ * q₀) * (x * a₀ * x⁻¹) * (p₀ * q₀)⁻¹
      = x * ((x⁻¹ * (p₀ * q₀) * x) * a₀ * (x⁻¹ * (p₀ * q₀) * x)⁻¹) * x⁻¹ := by group
    _ = x * a₀⁻¹ * x⁻¹ := by rw [hcc]
    _ = (x * a₀ * x⁻¹)⁻¹ := by group


theorem g_pow_half : ∃ M : ℕ, M + M = Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) ∧
    (x * a₀ * x⁻¹) ^ M = x * z * x⁻¹ := by
  have hVgen := V₁_eq_zpowers d.a_mem d.gen
  have hN2 : 2 ∣ Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := by
    have h1 := Subgroup.card_dvd_of_le (zpowers_le.2 c.z_mem_V₁)
    rwa [Nat.card_zpowers, orderOf_two_of_sq_one c.hz2 c.hz1] at h1
  obtain ⟨M, hM⟩ := hN2
  have hNpos : 0 < Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := Nat.card_pos
  have hM0 : M ≠ 0 := by omega
  have hNord : orderOf a₀ = Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) := by
    have : Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) = orderOf a₀ := by
      rw [hVgen]; exact Nat.card_zpowers a₀
    exact this.symm
  have haN : a₀ ^ Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) = 1 := by
    rw [← hNord]; exact pow_orderOf_eq_one a₀
  have haM2 : a₀ ^ M * a₀ ^ M = 1 := by
    rw [← pow_add, show M + M = Nat.card ↥(P ⊓ centralizer ({u₁} : Set G)) by omega]; exact haN
  have haM1 : a₀ ^ M ≠ 1 := pow_ne_one_of_lt_orderOf hM0 (by omega)
  have htz : a₀ ^ M = z :=
    B.cyclic_invol_unique c.V₁_cyc (Subgroup.pow_mem _ d.a_mem M) c.z_mem_V₁ haM2 c.hz2 haM1 c.hz1
  refine ⟨M, by omega, ?_⟩
  rw [conj_pow, htz]

theorem y_sq : ((x * a₀ * x⁻¹) * (p₀ * q₀)) * ((x * a₀ * x⁻¹) * (p₀ * q₀)) = 1 := by
  have h := d.u'_inv_g
  have hsq := d.u'_sq'
  calc ((x * a₀ * x⁻¹) * (p₀ * q₀)) * ((x * a₀ * x⁻¹) * (p₀ * q₀))
      = (x * a₀ * x⁻¹) * ((p₀ * q₀) * (x * a₀ * x⁻¹) * (p₀ * q₀)⁻¹) * ((p₀ * q₀) * (p₀ * q₀)) := by
        group
    _ = 1 := by rw [h, hsq]; group

theorem y_mem_S : (x * a₀ * x⁻¹) * (p₀ * q₀) ∈ S :=
  S.mul_mem (c.g_mem_S d.a_mem) (S.mul_mem (c.cfg.P_le d.p_mem) (c.cfg.Q_le d.q_mem))

theorem y_not_R : (x * a₀ * x⁻¹) * (p₀ * q₀) ∉ P ⊔ Q := by
  intro hy
  have hu : p₀ * q₀ ∈ P ⊔ Q := mul_mem (mem_sup_left d.p_mem) (mem_sup_right d.q_mem)
  apply c.g_not_R d.a_mem d.gen
  have := (P ⊔ Q).mul_mem hy ((P ⊔ Q).inv_mem hu)
  have e : (x * a₀ * x⁻¹) * (p₀ * q₀) * (p₀ * q₀)⁻¹ = x * a₀ * x⁻¹ := by group
  rw [e] at this
  exact this


theorem cent_Q {q : G} (hq : q ∈ Q)
    (hqy : ((x * a₀ * x⁻¹) * (p₀ * q₀)) * q = q * ((x * a₀ * x⁻¹) * (p₀ * q₀))) :
    q = 1 ∨ q = z := by
  by_cases hqV : q ∈ Q ⊓ centralizer ({u₂} : Set G)
  · have hqg : q * (x * a₀ * x⁻¹) = (x * a₀ * x⁻¹) * q := by
      simpa using c.V₂_comm_gpow d.a_mem d.gen hqV 1
    have hinv := c.u'_inv₂ d.p_mem d.q_mem d.q_not q hqV
    have h1 : ((x * a₀ * x⁻¹) * (p₀ * q₀)) * q * ((x * a₀ * x⁻¹) * (p₀ * q₀))⁻¹ = q := by
      rw [hqy]; group
    have hgq : (x * a₀ * x⁻¹) * q * (x * a₀ * x⁻¹)⁻¹ = q := by
      rw [← hqg]; group
    have h2 : ((x * a₀ * x⁻¹) * (p₀ * q₀)) * q * ((x * a₀ * x⁻¹) * (p₀ * q₀))⁻¹ = q⁻¹ := by
      calc ((x * a₀ * x⁻¹) * (p₀ * q₀)) * q * ((x * a₀ * x⁻¹) * (p₀ * q₀))⁻¹
          = (x * a₀ * x⁻¹) * ((p₀ * q₀) * q * (p₀ * q₀)⁻¹) * (x * a₀ * x⁻¹)⁻¹ := by group
        _ = (x * a₀ * x⁻¹) * q⁻¹ * (x * a₀ * x⁻¹)⁻¹ := by rw [hinv]
        _ = ((x * a₀ * x⁻¹) * q * (x * a₀ * x⁻¹)⁻¹)⁻¹ := by group
        _ = q⁻¹ := by rw [hgq]
    have h3 : q = q⁻¹ := by rw [← h2, h1]
    have h4 : q * q = 1 := by
      calc q * q = q * q⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel q
    exact c.Q_inv q hq h4
  · exfalso
    obtain ⟨hqsq, hqinv⟩ := c.quatOut₂ q hq hqV
    have hv : q₀ * q⁻¹ ∈ Q ⊓ centralizer ({u₂} : Set G) := by
      rcases B.mem_or_mul_inv_mem c.V₂_idx.le hq hqV d.q_mem with h | h
      · exact absurd h d.q_not
      · exact h
    obtain ⟨v, hvdef⟩ : ∃ v, v = q₀ * q⁻¹ := ⟨_, rfl⟩
    rw [← hvdef] at hv
    have hq₀ : q₀ = v * q := by rw [hvdef]; group
    have h2 := hqinv v⁻¹ (inv_mem hv)
    rw [inv_inv] at h2
    have hu'q : (p₀ * q₀) * q * (p₀ * q₀)⁻¹ = (v * v) * q := by
      have hcomm : p₀ * (q₀ * q * q₀⁻¹) = (q₀ * q * q₀⁻¹) * p₀ :=
        c.cfg.PQ_comm p₀ d.p_mem _ (Q.mul_mem (Q.mul_mem d.q_mem hq) (Q.inv_mem d.q_mem))
      have h1 : (p₀ * q₀) * q * (p₀ * q₀)⁻¹ = q₀ * q * q₀⁻¹ := by
        calc (p₀ * q₀) * q * (p₀ * q₀)⁻¹ = p₀ * (q₀ * q * q₀⁻¹) * p₀⁻¹ := by group
          _ = (q₀ * q * q₀⁻¹) * p₀ * p₀⁻¹ := by rw [hcomm]
          _ = q₀ * q * q₀⁻¹ := by group
      rw [h1, hq₀]
      calc (v * q) * q * (v * q)⁻¹ = v * (q * v⁻¹ * q⁻¹) * q := by group
        _ = v * v * q := by rw [h2]
    have hgvc : v * (x * a₀ * x⁻¹) = (x * a₀ * x⁻¹) * v := by
      simpa using c.V₂_comm_gpow d.a_mem d.gen hv 1
    have hgv' : (x * a₀ * x⁻¹) * v * (x * a₀ * x⁻¹)⁻¹ = v := by
      rw [← hgvc]; group
    have hyq : (x * a₀ * x⁻¹) * ((v * v) * q) * (x * a₀ * x⁻¹)⁻¹ = q := by
      have : (x * a₀ * x⁻¹) * ((p₀ * q₀) * q * (p₀ * q₀)⁻¹) * (x * a₀ * x⁻¹)⁻¹ = q := by
        calc _ = (((x * a₀ * x⁻¹) * (p₀ * q₀)) * q * ((x * a₀ * x⁻¹) * (p₀ * q₀))⁻¹) := by group
          _ = q := by rw [hqy]; group
      rwa [hu'q] at this
    have hgq : (x * a₀ * x⁻¹) * q * (x * a₀ * x⁻¹)⁻¹ = (v * v)⁻¹ * q := by
      have h5 : (x * a₀ * x⁻¹) * ((v * v) * q) * (x * a₀ * x⁻¹)⁻¹ =
          (v * v) * ((x * a₀ * x⁻¹) * q * (x * a₀ * x⁻¹)⁻¹) := by
        calc (x * a₀ * x⁻¹) * ((v * v) * q) * (x * a₀ * x⁻¹)⁻¹
            = ((x * a₀ * x⁻¹) * v * (x * a₀ * x⁻¹)⁻¹) * ((x * a₀ * x⁻¹) * v * (x * a₀ * x⁻¹)⁻¹) *
              ((x * a₀ * x⁻¹) * q * (x * a₀ * x⁻¹)⁻¹) := by group
          _ = _ := by rw [hgv']
      calc (x * a₀ * x⁻¹) * q * (x * a₀ * x⁻¹)⁻¹
          = (v * v)⁻¹ * ((v * v) * ((x * a₀ * x⁻¹) * q * (x * a₀ * x⁻¹)⁻¹)) := by group
        _ = (v * v)⁻¹ * q := by rw [← h5, hyq]
    obtain ⟨M, hM, hgM⟩ := d.g_pow_half
    have hz'q := c.z'_conj_q hq hqV
    have hgw : (x * a₀ * x⁻¹) * (v * v)⁻¹ * (x * a₀ * x⁻¹)⁻¹ = (v * v)⁻¹ := by
      calc (x * a₀ * x⁻¹) * (v * v)⁻¹ * (x * a₀ * x⁻¹)⁻¹
          = (((x * a₀ * x⁻¹) * v * (x * a₀ * x⁻¹)⁻¹) * ((x * a₀ * x⁻¹) * v * (x * a₀ * x⁻¹)⁻¹))⁻¹ := by
            group
        _ = (v * v)⁻¹ := by rw [hgv']
    generalize x * a₀ * x⁻¹ = g at hgq hgw hgM
    have hiter : ∀ j : ℕ, g ^ j * q * (g ^ j)⁻¹ = ((v * v)⁻¹) ^ j * q := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc g ^ (j + 1) * q * (g ^ (j + 1))⁻¹
            = g * (g ^ j * q * (g ^ j)⁻¹) * g⁻¹ := by
              rw [pow_succ']; group
          _ = g * (((v * v)⁻¹) ^ j * q) * g⁻¹ := by rw [ih]
          _ = (g * ((v * v)⁻¹) ^ j * g⁻¹) * (g * q * g⁻¹) := by group
          _ = ((v * v)⁻¹) ^ j * ((v * v)⁻¹ * q) := by
              rw [← conj_pow, hgw, hgq]
          _ = ((v * v)⁻¹) ^ (j + 1) * q := by rw [pow_succ]; group
    have hwM : ((v * v)⁻¹) ^ M = 1 := by
      have hvcard : v⁻¹ ^ Nat.card ↥(Q ⊓ centralizer ({u₂} : Set G)) = 1 := by
        have := pow_card_eq_one' (G := ↥(Q ⊓ centralizer ({u₂} : Set G))) (x := ⟨v⁻¹, inv_mem hv⟩)
        simpa using congrArg Subtype.val this
      rw [c.card_V₂, ← hM] at hvcard
      calc ((v * v)⁻¹) ^ M = (v⁻¹ * v⁻¹) ^ M := by rw [mul_inv_rev]
        _ = v⁻¹ ^ M * v⁻¹ ^ M := (Commute.refl v⁻¹).mul_pow M
        _ = v⁻¹ ^ (M + M) := by rw [pow_add]
        _ = 1 := hvcard
    have h6 := hiter M
    rw [hgM, hwM, one_mul] at h6
    rw [h6] at hz'q
    apply c.hz1
    have : z * q = 1 * q := by rw [← hz'q, one_mul]
    exact mul_right_cancel this

end Gd

theorem exists_y :
    ∃ y ∈ S, y * y = 1 ∧ y ∉ P ⊔ Q ∧ ∀ q ∈ Q, y * q = q * y → q = 1 ∨ q = z := by
  obtain ⟨a₀, ha₀V, hgen⟩ := exists_gen_of_cyclic c.V₁_cyc
  obtain ⟨p₀, hp₀, hp₀V⟩ := c.exists_notin_V₁
  obtain ⟨q₀, hq₀, hq₀V⟩ := c.exists_notin_V₂
  have d : Gd c a₀ p₀ q₀ := ⟨ha₀V, hgen, hp₀, hq₀, hp₀V, hq₀V⟩
  exact ⟨_, d.y_mem_S, d.y_sq, d.y_not_R, fun q hq hqy => d.cent_Q hq hqy⟩

theorem exists_y_sd
    (h1024 : Bg.B_maximalClass_of_small_centralizer) (hshape : Bg.B_two_maximalClass_shape) :
    ∃ y ∈ S, y * y = 1 ∧ y ∉ P ⊔ Q ∧ ∃ n, IVK.IsSemidihedralTwoGroup ↥(Q ⊔ zpowers y) n := by
  obtain ⟨y, hyS, hy2, hyR, hcent⟩ := c.exists_y
  have hyQ : y ∉ Q := fun h => hyR (mem_sup_right h)
  have hyn : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun q hq => c.cfg.Q_norm y hyS q hq
  obtain ⟨m, hm⟩ := sd_of_centralizer c.quatQ.choose_spec c.cfg.z_Q c.hz2 c.hz1 hy2 hyQ hyn hcent
    h1024 hshape
  exact ⟨y, hyS, hy2, hyR, m, hm⟩

end Setup9

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
