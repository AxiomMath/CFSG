module

public import CFSG.GH74.GLS.C3.Prop121.MooreBasic

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2

structure MCtx {G : Type} [Group G] (n : ℕ) (x : G) (K Q : Subgroup G) (t u g : G)
    (L : Subgroup G) (φ : Perm (Fin (n + 1)) →* G) : Prop where
  hn : n = 5 ∨ n = 6 ∨ n = 7
  S : Stage3Loc n x K Q t u g
  C : ThreeLocalCore K t u L
  P : PhiData K L u φ
  hc : φ (cEnd n) = g * t * g⁻¹

namespace MCtx

variable {G : Type} [Group G] {n : ℕ} {x : G} {K Q : Subgroup G} {t u g : G} {L : Subgroup G}
  {φ : Perm (Fin (n + 1)) →* G}

theorem n_ge (h : MCtx n x K Q t u g L φ) : 5 ≤ n := by
  rcases h.hn with rfl | rfl | rfl <;> norm_num

theorem g_inv (h : MCtx n x K Q t u g L φ) : g⁻¹ = g := sq_eq_one_inv h.S.g_sq

theorem x_mul_self (h : MCtx n x K Q t u g L φ) : x * x = 1 := by
  rw [← sq]; exact h.S.x_sq

theorem sup_le_cent_x (h : MCtx n x K Q t u g L φ) :
    K ⊔ zpowers u ≤ centralizer ({x} : Set G) := by
  refine sup_le (fun k hk => ?_) (zpowers_le.2 ?_)
  · rw [mem_centralizer_singleton_iff]
    exact h.S.K_comm_Q k hk x h.S.x_mem
  · rw [mem_centralizer_singleton_iff]
    exact h.S.u_comm_x

theorem stab_comm_x (h : MCtx n x K Q t u g L φ) {p : Perm (Fin (n + 1))} (hp : p 0 = 0) :
    φ p * x = x * φ p :=
  mem_centralizer_singleton_iff.1 (h.sup_le_cent_x ((h.P.stab p).2 hp))

theorem odd_inv_t (h : MCtx n x K Q t u g L φ) {p : Perm (Fin (n + 1))} (hp : sign p = -1) :
    φ p * t * (φ p)⁻¹ = t⁻¹ := by
  have hY := h.P.mem p
  rcases (CFSG.GH74.GLS.C3.Layer2.mem_sup_zpowers_iff h.C.u_norm_L h.S.u_sq).1 hY with hL | hL
  · exfalso
    have := (h.P.alt p).1 hL
    rw [hp] at this
    exact absurd this (by decide)
  · have hφ : φ p = (φ p * u⁻¹) * u := by group
    have hlt : Commute (φ p * u⁻¹) t := h.C.L_comm_t _ hL
    have hlt' : (φ p * u⁻¹) * t⁻¹ = t⁻¹ * (φ p * u⁻¹) := hlt.inv_right
    rw [hφ]
    calc (φ p * u⁻¹) * u * t * ((φ p * u⁻¹) * u)⁻¹
        = (φ p * u⁻¹) * (u * t * u⁻¹) * (φ p * u⁻¹)⁻¹ := by group
      _ = (φ p * u⁻¹) * t⁻¹ * (φ p * u⁻¹)⁻¹ := by rw [h.S.u_inv_t]
      _ = t⁻¹ := by rw [hlt']; group

theorem mem_L_of_comm (h : MCtx n x K Q t u g L φ) {a : G} (ha2 : a * a = 1)
    (hat : a * t = t * a) : a ∈ L := by
  obtain ⟨i, l, hl, rfl⟩ := h.C.C_eq a hat
  have hcomm : l * t ^ i = t ^ i * l := ((show Commute l t from h.C.L_comm_t l hl).zpow_right i)
  have h1 : t ^ (i + i) * (l * l) = 1 := by
    calc t ^ (i + i) * (l * l) = t ^ i * t ^ i * (l * l) := by rw [zpow_add]
      _ = t ^ i * (t ^ i * l) * l := by group
      _ = t ^ i * (l * t ^ i) * l := by rw [← hcomm]
      _ = (t ^ i * l) * (t ^ i * l) := by group
      _ = 1 := ha2
  have h2 : t ^ (i + i) = (l * l)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : t ^ (i + i) ∈ L := by rw [h2]; exact L.inv_mem (L.mul_mem hl hl)
  have h4 := h.C.zpowers_inf_L _ h3
  have hdvd : (orderOf t : ℤ) ∣ (i + i) := orderOf_dvd_iff_zpow_eq_one.2 h4
  rw [h.S.t_order] at hdvd
  have h5 : (3 : ℤ) ∣ i := by push_cast at hdvd; omega
  have h6 : t ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [h.S.t_order]; exact_mod_cast h5)
  rw [h6, one_mul]; exact hl

theorem t_comm_tg (h : MCtx n x K Q t u g L φ) : t * (g * t * g⁻¹) = (g * t * g⁻¹) * t :=
  h.S.t_comm_K _ h.S.gt_K

theorem xg_mem (h : MCtx n x K Q t u g L φ) : g * x * g⁻¹ ∈ K := h.S.g_Q x h.S.x_mem

theorem t_comm_xg (h : MCtx n x K Q t u g L φ) : t * (g * x * g⁻¹) = (g * x * g⁻¹) * t :=
  h.S.t_comm_K _ h.xg_mem

theorem K_le_Y (h : MCtx n x K Q t u g L φ) : K ≤ L ⊔ zpowers u :=
  h.C.K_le_L.trans le_sup_left

theorem cs_comm_cEnd (n : ℕ) {k : ℕ} (hk : k + 4 ≤ n) : cs n k * cEnd n = cEnd n * cs n k := by
  unfold cEnd
  calc cs n k * (cs n (n - 2) * cs n (n - 1)) = (cs n k * cs n (n - 2)) * cs n (n - 1) :=
        (mul_assoc _ _ _).symm
    _ = (cs n (n - 2) * cs n k) * cs n (n - 1) := by rw [cs_comm n (by omega : k + 2 ≤ n - 2)]
    _ = cs n (n - 2) * (cs n k * cs n (n - 1)) := mul_assoc _ _ _
    _ = cs n (n - 2) * (cs n (n - 1) * cs n k) := by rw [cs_comm n (by omega : k + 2 ≤ n - 1)]
    _ = (cs n (n - 2) * cs n (n - 1)) * cs n k := (mul_assoc _ _ _).symm

theorem a_mem_L (h : MCtx n x K Q t u g L φ) {k : ℕ} (hk : k + 4 ≤ n) :
    g * φ (cs n k) * g⁻¹ ∈ L := by
  have hcomm : φ (cs n k) * (g * t * g⁻¹) = (g * t * g⁻¹) * φ (cs n k) := by
    rw [← h.hc, ← map_mul, ← map_mul, cs_comm_cEnd n hk]
  have h1 : (g * φ (cs n k) * g⁻¹) * t = t * (g * φ (cs n k) * g⁻¹) := by
    have this : g * (φ (cs n k) * (g * t * g⁻¹)) * g⁻¹ =
        g * ((g * t * g⁻¹) * φ (cs n k)) * g⁻¹ := by rw [hcomm]
    have e1 : g * (φ (cs n k) * (g * t * g⁻¹)) * g⁻¹ =
        (g * φ (cs n k) * g⁻¹) * (g * (g * t * g⁻¹) * g⁻¹) := by group
    have e2 : g * ((g * t * g⁻¹) * φ (cs n k)) * g⁻¹ =
        (g * (g * t * g⁻¹) * g⁻¹) * (g * φ (cs n k) * g⁻¹) := by group
    rw [e1, e2, conj_conj_invol h.S.g_sq t] at this
    exact this
  have h2 : (g * φ (cs n k) * g⁻¹) * (g * φ (cs n k) * g⁻¹) = 1 := by
    calc (g * φ (cs n k) * g⁻¹) * (g * φ (cs n k) * g⁻¹) = g * (φ (cs n k) * φ (cs n k)) * g⁻¹ := by
          group
      _ = 1 := by rw [← map_mul, cs_mul_self, map_one]; group
  exact h.mem_L_of_comm h2 h1

theorem a_inv_tg (h : MCtx n x K Q t u g L φ) {k : ℕ} (hk : k < n) :
    (g * φ (cs n k) * g⁻¹) * (g * t * g⁻¹) * (g * φ (cs n k) * g⁻¹)⁻¹ = (g * t * g⁻¹)⁻¹ := by
  calc (g * φ (cs n k) * g⁻¹) * (g * t * g⁻¹) * (g * φ (cs n k) * g⁻¹)⁻¹
      = g * (φ (cs n k) * t * (φ (cs n k))⁻¹) * g⁻¹ := by group
    _ = g * t⁻¹ * g⁻¹ := by rw [h.odd_inv_t (sign_cs hk)]
    _ = (g * t * g⁻¹)⁻¹ := by group

theorem a_comm_xg (h : MCtx n x K Q t u g L φ) {k : ℕ} (hk1 : 1 ≤ k) :
    (g * φ (cs n k) * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * φ (cs n k) * g⁻¹) := by
  have h0 := h.stab_comm_x (cs_apply_zero hk1)
  calc (g * φ (cs n k) * g⁻¹) * (g * x * g⁻¹) = g * (φ (cs n k) * x) * g⁻¹ := by group
    _ = g * (x * φ (cs n k)) * g⁻¹ := by rw [h0]
    _ = (g * x * g⁻¹) * (g * φ (cs n k) * g⁻¹) := by group

theorem a_braid {k : ℕ} (hk : k + 1 < n) :
    ((g * φ (cs n k) * g⁻¹) * (g * φ (cs n (k + 1)) * g⁻¹)) ^ 3 = 1 := by
  have e : (g * φ (cs n k) * g⁻¹) * (g * φ (cs n (k + 1)) * g⁻¹) =
      g * (φ (cs n k) * φ (cs n (k + 1))) * g⁻¹ := by group
  rw [e, conj_pow, ← map_mul, ← map_pow, cs_braid n hk, map_one]
  group

theorem a_sq2 {k l : ℕ} (hkl : k + 2 ≤ l) :
    ((g * φ (cs n k) * g⁻¹) * (g * φ (cs n l) * g⁻¹)) ^ 2 = 1 := by
  have e : (g * φ (cs n k) * g⁻¹) * (g * φ (cs n l) * g⁻¹) =
      g * (φ (cs n k) * φ (cs n l)) * g⁻¹ := by group
  have h2 : (cs n k * cs n l) ^ 2 = 1 := by
    calc (cs n k * cs n l) ^ 2 = cs n k * cs n l * (cs n k * cs n l) := sq _
      _ = cs n k * (cs n l * cs n k) * cs n l := by group
      _ = cs n k * (cs n k * cs n l) * cs n l := by rw [(cs_comm n hkl).symm]
      _ = (cs n k * cs n k) * (cs n l * cs n l) := by group
      _ = 1 := by rw [cs_mul_self, cs_mul_self, mul_one]
  rw [e, conj_pow, ← map_mul, ← map_pow, h2, map_one]
  group

theorem a_ne (h : MCtx n x K Q t u g L φ) {k l : ℕ} (hk : k < n) (hl : l < n) (hne : k ≠ l) :
    g * φ (cs n k) * g⁻¹ ≠ g * φ (cs n l) * g⁻¹ := by
  intro heq
  have h1 : φ (cs n k) = φ (cs n l) := by
    have := congrArg (fun z => g⁻¹ * z * g) heq
    simpa [mul_assoc] using this
  exact hne (cs_injective hk hl (h.P.inj h1))

end MCtx

end CFSG.GH74.GLS.C3.Prop121
