module

public import CFSG.GH74.GLS.Stage4.T2FnH
public import CFSG.GH74.GLS.Stage4.T2Omega1
public import CFSG.GH74.GLS.Stage4.T2P53a
public import CFSG.GH74.GLS.Stage4.T2P53d

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.Stage4.Hex

section Def

variable {G : Type} [Group G]

structure T2Four (z u : G) (K₁ K₂ H : Subgroup G) (w₁ w₂ : G) : Prop where
  zz : z * z = 1
  z_ne : z ≠ 1
  uu : u * u = 1
  u_ne : u ≠ 1
  zu_ne : z ≠ u
  zu_comm : z * u = u * z
  K_comm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  K_inter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z
  K_le_C : K₁ ⊔ K₂ ≤ centralizer ({z} : Set G)
  C_norm₁ : ∀ c ∈ centralizer ({z} : Set G), ∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁
  C_norm₂ : ∀ c ∈ centralizer ({z} : Set G), ∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂
  C_idx : (K₁ ⊔ K₂).relIndex (centralizer ({z} : Set G)) = 2
  H_comm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x
  z_mem_H : z ∈ H
  u_mem_H : u ∈ H
  H_le_C : H ≤ centralizer ({z} : Set G)
  H_not_le_K : ¬ H ≤ K₁ ⊔ K₂
  H₁_iff : ∀ x ∈ K₁, x ∈ H ↔ x * u = u * x
  H₂_iff : ∀ x ∈ K₂, x ∈ H ↔ x * u = u * x
  w₁_mem : w₁ ∈ K₁
  w₂_mem : w₂ ∈ K₂
  w₁_sq : w₁ * w₁ = z
  w₂_sq : w₂ * w₂ = z
  w₁_u : w₁ * u * w₁⁻¹ = u * z
  w₂_u : w₂ * u * w₂⁻¹ = u * z
  w₁_normH : ∀ h ∈ H, w₁ * h * w₁⁻¹ ∈ H
  w₂_normH : ∀ h ∈ H, w₂ * h * w₂⁻¹ ∈ H
  w₀_inv : ∀ h ∈ H, (w₁ * w₂) * h * (w₁ * w₂)⁻¹ = h⁻¹
  w₀_not_mem : w₁ * w₂ ∉ H

namespace T2Four

variable {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G} (h : T2Four z u K₁ K₂ H w₁ w₂)
include h

theorem z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.zz

theorem u_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right h.uu

theorem w₁_z : w₁ * z = z * w₁ :=
  Subgroup.mem_centralizer_singleton_iff.1 (h.K_le_C (Subgroup.mem_sup_left h.w₁_mem))

theorem w₂_z : w₂ * z = z * w₂ :=
  Subgroup.mem_centralizer_singleton_iff.1 (h.K_le_C (Subgroup.mem_sup_right h.w₂_mem))

theorem w₁w₂_comm : w₁ * w₂ = w₂ * w₁ := h.K_comm w₁ h.w₁_mem w₂ h.w₂_mem

theorem u_mem_C : u ∈ centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 h.zu_comm.symm

theorem w₀_sq : (w₁ * w₂) * (w₁ * w₂) = 1 := by
  calc (w₁ * w₂) * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
    _ = w₁ * (w₁ * w₂) * w₂ := by rw [← h.w₁w₂_comm]
    _ = (w₁ * w₁) * (w₂ * w₂) := by group
    _ = 1 := by rw [h.w₁_sq, h.w₂_sq, h.zz]

theorem w₀_inv_self : (w₁ * w₂)⁻¹ = w₁ * w₂ := inv_eq_of_mul_eq_one_right h.w₀_sq

theorem w₀_z : (w₁ * w₂) * z = z * (w₁ * w₂) := by
  calc (w₁ * w₂) * z = w₁ * (w₂ * z) := by group
    _ = w₁ * (z * w₂) := by rw [h.w₂_z]
    _ = (w₁ * z) * w₂ := by group
    _ = (z * w₁) * w₂ := by rw [h.w₁_z]
    _ = z * (w₁ * w₂) := by group

theorem w₁_z' : w₁ * z * w₁⁻¹ = z := by
  calc w₁ * z * w₁⁻¹ = z * w₁ * w₁⁻¹ := by rw [h.w₁_z]
    _ = z := by group

theorem w₀_u : (w₁ * w₂) * u = u * (w₁ * w₂) := by
  have h1 : (w₁ * w₂) * u * (w₁ * w₂)⁻¹ = u := by
    calc (w₁ * w₂) * u * (w₁ * w₂)⁻¹ = w₁ * (w₂ * u * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * (u * z) * w₁⁻¹ := by rw [h.w₂_u]
      _ = (w₁ * u * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
      _ = (u * z) * z := by rw [h.w₁_u, h.w₁_z']
      _ = u * (z * z) := by group
      _ = u := by rw [h.zz, mul_one]
  calc (w₁ * w₂) * u = ((w₁ * w₂) * u * (w₁ * w₂)⁻¹) * (w₁ * w₂) := by group
    _ = u * (w₁ * w₂) := by rw [h1]

theorem w₁_w₀ : w₁ * (w₁ * w₂) = (w₁ * w₂) * w₁ := by
  calc w₁ * (w₁ * w₂) = w₁ * (w₂ * w₁) := by rw [h.w₁w₂_comm]
    _ = (w₁ * w₂) * w₁ := by group

theorem w₀_mem_C : w₁ * w₂ ∈ centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 h.w₀_z

theorem w₀_mem_K : w₁ * w₂ ∈ K₁ ⊔ K₂ :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_left h.w₁_mem) (Subgroup.mem_sup_right h.w₂_mem)

theorem Hw_sq {x : G} (hx : x ∈ H) : (x * (w₁ * w₂)) * (x * (w₁ * w₂)) = 1 := by
  have h1 := h.w₀_inv x hx
  rw [h.w₀_inv_self] at h1
  calc (x * (w₁ * w₂)) * (x * (w₁ * w₂)) = x * ((w₁ * w₂) * x * (w₁ * w₂)) := by group
    _ = x * x⁻¹ := by rw [h1]
    _ = 1 := by group

theorem Y1 : ∀ y ∈ centralizer ({z} : Set G), y * u = u * y →
    y ∈ H ∨ ∃ x ∈ H, y = x * (w₁ * w₂) := by
  obtain ⟨s₀, hs₀H, hs₀K⟩ := IsConcreteLE.not_le_iff_exists.1 h.H_not_le_K
  exact t2C_Y1 (C₁ := centralizer ({z} : Set G)) (H := H) (z := z) (u := u) (w₁ := w₁)
    (w₂ := w₂) h.K_comm h.K_inter h.zz (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx)
    h.K_le_C h.u_mem_C h.C_norm₁ h.C_norm₂ h.uu h.w₁_mem h.w₂_mem h.w₁_u h.w₂_u h.H₁_iff h.H₂_iff
    h.H_comm h.u_mem_H h.H_le_C h.w₀_inv h.C_idx hs₀H hs₀K

end T2Four

end Def

section Y

variable {G : Type} [Group G] [Finite G] {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}
  (h : T2Four z u K₁ K₂ H w₁ w₂)
include h

namespace T2Four

theorem omega1 (hr : CFSG.pRank 2 G = 3) :
    ∀ x ∈ H, x * x = 1 → x = 1 ∨ x = z ∨ x = u ∨ x = z * u :=
  t2_omega1_zu hr h.H_comm h.z_mem_H h.u_mem_H h.zz h.uu h.z_ne h.u_ne h.zu_ne h.w₀_sq
    h.w₀_not_mem h.w₀_inv

theorem inv_mem_Hw (hr : CFSG.pRank 2 G = 3) {y : G} (hyz : y * z = z * y) (hyu : y * u = u * y)
    (hy2 : y * y = 1) (hyU : ¬ (y = 1 ∨ y = z ∨ y = u ∨ y = z * u)) :
    ∃ x ∈ H, y = x * (w₁ * w₂) := by
  refine t2Y_inv (F := ⊥) (H := H) (z := z) (u := u) (w₀ := w₁ * w₂) ?_ ?_ ?_ ?_ h.w₀_sq
    h.w₀_inv (h.omega1 hr) hyz hyu hy2 hyU
  · intro y' hyz' hyu'
    exact ⟨y', 1, Subgroup.one_mem _,
      h.Y1 y' (Subgroup.mem_centralizer_singleton_iff.2 hyz') hyu', by simp⟩
  · intro f hf
    rw [Subgroup.mem_bot.1 hf, orderOf_one]
    exact odd_one
  · intro f hf
    rw [Subgroup.mem_bot.1 hf]
    simp
  · intro f hf x hx
    rw [Subgroup.mem_bot.1 hf]
    simpa using hx

theorem normH (hr : CFSG.pRank 2 G = 3) {t : G} (ht : t ∈ normalizer (t2U z u : Set G)) :
    ∀ x ∈ H, t * x * t⁻¹ ∈ H :=
  t2Y_normH (H := H) (z := z) (u := u) (w₀ := w₁ * w₂) (t := t)
    (fun _ hyz hyu hy2 hyU => h.inv_mem_Hw hr hyz hyu hy2 hyU) h.H_comm h.z_mem_H h.u_mem_H
    h.w₀_sq h.w₀_not_mem h.w₀_z h.w₀_u h.w₀_inv (t2U_conj_inv h.zz h.uu h.zu_comm ht)

theorem exists_a (hr : CFSG.pRank 2 G = 3) {F₁ : Type} [Field F₁] [Finite F₁]
    (hodd : Odd (Nat.card F₁)) (h3 : 3 < Nat.card F₁) (e₁ : ↥K₁ ≃* SL2 F₁)
    (hK₁inv : ∀ x ∈ K₁, x * x = 1 → x = 1 ∨ x = z)
    (hnc : ∀ y : G, y * y = 1 → y * z = z * y → y ≠ 1 → y ≠ z → ∃ x ∈ K₁, y * x * y⁻¹ ≠ x)
    (hconj : ∃ g : G, g⁻¹ * z * g = u) :
    ∃ a : G, a⁻¹ * z * a = u ∧ a⁻¹ * u * a = z * u ∧ a ∈ normalizer (H : Set G) ∧ a ^ 3 ∈ H ∧
      (∃ x ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * x) ∧ (∃ x ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * x) := by
  obtain ⟨g, hg⟩ := hconj
  have hy2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.zz]; group
  have hyz : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
    have hz : z = g * u * g⁻¹ := by rw [← hg]; group
    calc (g * z * g⁻¹) * z = g * z * g⁻¹ * (g * u * g⁻¹) := by rw [← hz]
      _ = g * (z * u) * g⁻¹ := by group
      _ = g * (u * z) * g⁻¹ := by rw [h.zu_comm]
      _ = (g * u * g⁻¹) * (g * z * g⁻¹) := by group
      _ = z * (g * z * g⁻¹) := by rw [← hz]
  have hy1 : g * z * g⁻¹ ≠ 1 := by
    intro h1
    apply h.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hyne : g * z * g⁻¹ ≠ z := by
    intro h1
    apply h.zu_ne
    have : g * z = z * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [h1]
    calc z = g⁻¹ * (g * z) := by group
      _ = g⁻¹ * (z * g) := by rw [this]
      _ = u := by rw [← hg]; group
  have hnc' := hnc _ hy2 hyz hy1 hyne
  have hnorm : ∀ c : G, c * z = z * c → ∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁ :=
    fun c hc => h.C_norm₁ c (Subgroup.mem_centralizer_singleton_iff.2 hc)
  obtain ⟨v, hvv, hvz⟩ := t2P53_v hodd h3 e₁ h.zz h.zu_comm hg hnorm hK₁inv hnc'
  have hdec : ∀ y : G, y * z = z * y → y * u = u * y →
      ∃ k f : G, f ∈ (⊥ : Subgroup G) ∧ (k ∈ H ∨ ∃ x ∈ H, k = x * (w₁ * w₂)) ∧ y = k * f :=
    fun y hyz hyu => ⟨y, 1, Subgroup.one_mem _,
      h.Y1 y (Subgroup.mem_centralizer_singleton_iff.2 hyz) hyu, by simp⟩
  obtain ⟨a, d1, d2, haN, ha3, hw₁a, hw₂a, -, -⟩ :=
    t2P53_core (H := H) (F := ⊥) (w₀ := w₁ * w₂) rfl h.zz h.uu h.zu_comm h.w₁_z h.w₁_u h.w₁_sq
      h.w₂_z h.w₂_u h.w₁w₂_comm hvv hvz h.H_comm h.z_mem_H h.u_mem_H h.w₁_normH h.w₂_normH h.w₀_sq
      h.w₀_not_mem h.w₀_inv (h.omega1 hr)
      (fun f hf => by rw [Subgroup.mem_bot.1 hf, orderOf_one]; exact odd_one)
      (fun f hf => by rw [Subgroup.mem_bot.1 hf]; simp)
      (fun f hf => by rw [Subgroup.mem_bot.1 hf]; simp)
      (fun f hf => by rw [Subgroup.mem_bot.1 hf]; simp)
      (fun f hf => by rw [Subgroup.mem_bot.1 hf]; simp)
      (fun f hf x hx => by rw [Subgroup.mem_bot.1 hf]; simpa using hx) hdec
  exact ⟨a, d1, d2, haN, ha3, hw₁a, hw₂a⟩

end T2Four

end Y

end CFSG.GH74.GLS.Stage4.Rest
