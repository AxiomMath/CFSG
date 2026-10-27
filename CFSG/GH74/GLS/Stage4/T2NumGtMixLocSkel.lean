module

public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeSkel
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage4.Rest.T2

section Skel

variable {G : Type} [Group G] {C₁ : Subgroup G} {c₁ c₂ : ℕ} {z : G} {K₁ K₂ T₁ T₂ : Subgroup G}
  {x₁ x₂ w₁ w₂ s : G} (sk : MixSkel C₁ c₁ c₂ z K₁ K₂ T₁ T₂ x₁ x₂ w₁ w₂ s)

include sk

theorem MixSkel.T₁₂_comm (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x := fun x hx y hy => hc x (sk.T₁_le hx) y (sk.T₂_le hy)

theorem MixSkel.A_comm (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ T₁ ⊔ T₂, x * y = y * x :=
  t2B_sup_comm (t2B_cyclic_comm T₁ sk.T₁_cyc) (t2B_cyclic_comm T₂ sk.T₂_cyc) (sk.T₁₂_comm hc)

theorem MixSkel.A_s_comm : ∀ x ∈ T₁ ⊔ T₂, x * s = s * x := by
  have : T₁ ⊔ T₂ ≤ centralizer ({s} : Set G) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (sk.s_comm₁ x hx).symm)
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (sk.s_comm₂ x hx).symm)
  exact fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (this hx)

theorem MixSkel.A_S_comm : ∀ x ∈ T₁ ⊔ T₂, ∀ y ∈ Subgroup.zpowers s, x * y = y * x := by
  intro x hx y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hxs : Commute x s := sk.A_s_comm x hx
  exact (hxs.zpow_right n).eq

theorem MixSkel.H_comm (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∀ x ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s, ∀ y ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s, x * y = y * x := by
  have hZc : ∀ x ∈ Subgroup.zpowers s, ∀ y ∈ Subgroup.zpowers s, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self s m n).eq
  exact t2B_sup_comm (sk.A_comm hc) hZc sk.A_S_comm

theorem MixSkel.exists_decomp (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {x : G}
    (hx : x ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s) :
    ∃ a ∈ T₁, ∃ b ∈ T₂, ∃ k : ℤ, x = a * b * s ^ k := by
  obtain ⟨p, hp, c, hc', rfl⟩ := (mem_sup_iff_of_comm sk.A_S_comm x).1 hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm (sk.T₁₂_comm hc) p).1 hp
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
  exact ⟨a, ha, b, hb, k, rfl⟩

theorem MixSkel.u_mem_H : x₁ * x₂ ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s :=
  Subgroup.mul_mem _ (skel_T₁_le_H sk.x₁_mem) (skel_T₂_le_H sk.x₂_mem)

theorem MixSkel.z_mem_H : z ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s :=
  sk.x₁_sq ▸ Subgroup.mul_mem _ (skel_T₁_le_H sk.x₁_mem) (skel_T₁_le_H sk.x₁_mem)

theorem MixSkel.w₁_inv' {y : G} (hy : y ∈ T₁) : w₁⁻¹ * y * w₁ = y⁻¹ := by
  have h : w₁ * y⁻¹ * w₁⁻¹ = y := by
    have := sk.w₁_inv y⁻¹ (T₁.inv_mem hy)
    rwa [inv_inv] at this
  calc w₁⁻¹ * y * w₁ = w₁⁻¹ * (w₁ * y⁻¹ * w₁⁻¹) * w₁ := by rw [h]
    _ = y⁻¹ := by group

theorem MixSkel.w₂_inv' {y : G} (hy : y ∈ T₂) : w₂⁻¹ * y * w₂ = y⁻¹ := by
  have h : w₂ * y⁻¹ * w₂⁻¹ = y := by
    have := sk.w₂_inv y⁻¹ (T₂.inv_mem hy)
    rwa [inv_inv] at this
  calc w₂⁻¹ * y * w₂ = w₂⁻¹ * (w₂ * y⁻¹ * w₂⁻¹) * w₂ := by rw [h]
    _ = y⁻¹ := by group

theorem MixSkel.w₁_conj_T₂ (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {y : G} (hy : y ∈ T₂) :
    w₁ * y * w₁⁻¹ = y := by
  rw [hc w₁ sk.w₁_mem y (sk.T₂_le hy)]
  group

theorem MixSkel.w₁_conj_T₂' (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {y : G} (hy : y ∈ T₂) :
    w₁⁻¹ * y * w₁ = y := by
  have h := hc w₁ sk.w₁_mem y (sk.T₂_le hy)
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem MixSkel.w₂_conj_T₁ (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {y : G} (hy : y ∈ T₁) :
    w₂ * y * w₂⁻¹ = y := by
  rw [← hc y (sk.T₁_le hy) w₂ sk.w₂_mem]
  group

theorem MixSkel.w₂_conj_T₁' (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {y : G} (hy : y ∈ T₁) :
    w₂⁻¹ * y * w₂ = y := by
  have h := hc y (sk.T₁_le hy) w₂ sk.w₂_mem
  rw [mul_assoc, h, inv_mul_cancel_left]

theorem MixSkel.w₀_inv (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    ∀ h ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s, (w₁ * w₂) * h * (w₁ * w₂)⁻¹ = h⁻¹ := by
  intro h hh
  obtain ⟨a, ha, b, hb, k, rfl⟩ := sk.exists_decomp hc hh
  have e1 : (w₁ * w₂) * a * (w₁ * w₂)⁻¹ = a⁻¹ := by
    calc (w₁ * w₂) * a * (w₁ * w₂)⁻¹ = w₁ * (w₂ * a * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * a * w₁⁻¹ := by rw [sk.w₂_conj_T₁ hc ha]
      _ = a⁻¹ := sk.w₁_inv a ha
  have e2 : (w₁ * w₂) * b * (w₁ * w₂)⁻¹ = b⁻¹ := by
    calc (w₁ * w₂) * b * (w₁ * w₂)⁻¹ = w₁ * (w₂ * b * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * b⁻¹ * w₁⁻¹ := by rw [sk.w₂_inv b hb]
      _ = b⁻¹ := sk.w₁_conj_T₂ hc (T₂.inv_mem hb)
  have e3 : (w₁ * w₂) * s ^ k * (w₁ * w₂)⁻¹ = (s ^ k)⁻¹ := by
    rw [← conj_zpow, sk.w₀_s, inv_zpow]
  have hH := sk.H_comm hc
  have hcH : s ^ k ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s :=
    Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers s k)
  have hab : a * b = b * a := hH a (skel_T₁_le_H ha) b (skel_T₂_le_H hb)
  have hac : a * s ^ k = s ^ k * a := hH a (skel_T₁_le_H ha) _ hcH
  have hbc : b * s ^ k = s ^ k * b := hH b (skel_T₂_le_H hb) _ hcH
  rw [skel_inv_mul3 hab hac hbc]
  calc (w₁ * w₂) * (a * b * s ^ k) * (w₁ * w₂)⁻¹
      = ((w₁ * w₂) * a * (w₁ * w₂)⁻¹) * ((w₁ * w₂) * b * (w₁ * w₂)⁻¹) *
          ((w₁ * w₂) * s ^ k * (w₁ * w₂)⁻¹) := by group
    _ = a⁻¹ * b⁻¹ * (s ^ k)⁻¹ := by rw [e1, e2, e3]

theorem MixSkel.conj_s_comm₁ {w : G} (hw : ∀ y ∈ T₁, w⁻¹ * y * w ∈ T₁) {y : G} (hy : y ∈ T₁) :
    (w * s * w⁻¹) * y = y * (w * s * w⁻¹) := by
  have h := sk.s_comm₁ (w⁻¹ * y * w) (hw y hy)
  calc w * s * w⁻¹ * y = w * (s * (w⁻¹ * y * w)) * w⁻¹ := by group
    _ = w * ((w⁻¹ * y * w) * s) * w⁻¹ := by rw [h]
    _ = y * (w * s * w⁻¹) := by group

theorem MixSkel.conj_s_comm₂ {w : G} (hw : ∀ y ∈ T₂, w⁻¹ * y * w ∈ T₂) {y : G} (hy : y ∈ T₂) :
    (w * s * w⁻¹) * y = y * (w * s * w⁻¹) := by
  have h := sk.s_comm₂ (w⁻¹ * y * w) (hw y hy)
  calc w * s * w⁻¹ * y = w * (s * (w⁻¹ * y * w)) * w⁻¹ := by group
    _ = w * ((w⁻¹ * y * w) * s) * w⁻¹ := by rw [h]
    _ = y * (w * s * w⁻¹) := by group

theorem MixSkel.conj_s_mem (hq₁ : 3 ≤ c₁) (hq₂ : 3 ≤ c₂) (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hKC : K₁ ⊔ K₂ ≤ C₁) (hidx : (K₁ ⊔ K₂).relIndex C₁ = 2) {w : G} (hwK : w ∈ K₁ ⊔ K₂)
    (hwT₁ : ∀ y ∈ T₁, w⁻¹ * y * w ∈ T₁) (hwT₂ : ∀ y ∈ T₂, w⁻¹ * y * w ∈ T₂) :
    w * s * w⁻¹ ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s := by
  have hs'C : w * s * w⁻¹ ∈ C₁ :=
    C₁.mul_mem (C₁.mul_mem (hKC hwK) sk.s_mem) (C₁.inv_mem (hKC hwK))
  have hs'K : w * s * w⁻¹ ∉ K₁ ⊔ K₂ := by
    intro h
    apply sk.s_not_mem
    have := (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).inv_mem hwK) h) hwK
    have e : w⁻¹ * (w * s * w⁻¹) * w = s := by group
    rwa [e] at this
  have hd : w * s * w⁻¹ * s⁻¹ ∈ K₁ ⊔ K₂ :=
    skel_mul_inv_mem hidx hs'C sk.s_mem hs'K sk.s_not_mem
  have hdT₁ : ∀ y ∈ T₁, (w * s * w⁻¹ * s⁻¹) * y = y * (w * s * w⁻¹ * s⁻¹) := by
    intro y hy
    have h2 : s⁻¹ * y = y * s⁻¹ := (Commute.inv_left (sk.s_comm₁ y hy : Commute s y)).eq
    calc w * s * w⁻¹ * s⁻¹ * y = (w * s * w⁻¹) * (s⁻¹ * y) := by group
      _ = (w * s * w⁻¹) * (y * s⁻¹) := by rw [h2]
      _ = ((w * s * w⁻¹) * y) * s⁻¹ := by group
      _ = (y * (w * s * w⁻¹)) * s⁻¹ := by rw [sk.conj_s_comm₁ hwT₁ hy]
      _ = y * (w * s * w⁻¹ * s⁻¹) := by group
  have hdT₂ : ∀ y ∈ T₂, (w * s * w⁻¹ * s⁻¹) * y = y * (w * s * w⁻¹ * s⁻¹) := by
    intro y hy
    have h2 : s⁻¹ * y = y * s⁻¹ := (Commute.inv_left (sk.s_comm₂ y hy : Commute s y)).eq
    calc w * s * w⁻¹ * s⁻¹ * y = (w * s * w⁻¹) * (s⁻¹ * y) := by group
      _ = (w * s * w⁻¹) * (y * s⁻¹) := by rw [h2]
      _ = ((w * s * w⁻¹) * y) * s⁻¹ := by group
      _ = (y * (w * s * w⁻¹)) * s⁻¹ := by rw [sk.conj_s_comm₂ hwT₂ hy]
      _ = y * (w * s * w⁻¹ * s⁻¹) := by group
  obtain ⟨k₁, hk₁, k₂, hk₂, hdk⟩ := (mem_sup_iff_of_comm hc _).1 hd
  obtain ⟨y₁, hy₁, hy₁y⟩ := skel_exists_sq_ne sk.T₁_cyc (by rw [sk.T₁_card]; exact hq₁)
  obtain ⟨y₂, hy₂, hy₂y⟩ := skel_exists_sq_ne sk.T₂_cyc (by rw [sk.T₂_card]; exact hq₂)
  have hk₁y : k₁ * y₁ = y₁ * k₁ := by
    have h1 : (k₁ * k₂) * y₁ = y₁ * (k₁ * k₂) := hdk ▸ hdT₁ y₁ hy₁
    have h2 : y₁ * k₂ = k₂ * y₁ := hc y₁ (sk.T₁_le hy₁) k₂ hk₂
    apply mul_right_cancel (b := k₂)
    calc k₁ * y₁ * k₂ = k₁ * (y₁ * k₂) := by rw [mul_assoc]
      _ = k₁ * (k₂ * y₁) := by rw [h2]
      _ = (k₁ * k₂) * y₁ := by rw [mul_assoc]
      _ = y₁ * (k₁ * k₂) := h1
      _ = y₁ * k₁ * k₂ := by rw [mul_assoc]
  have hk₂y : k₂ * y₂ = y₂ * k₂ := by
    have h1 : (k₁ * k₂) * y₂ = y₂ * (k₁ * k₂) := hdk ▸ hdT₂ y₂ hy₂
    have h2 : k₁ * y₂ = y₂ * k₁ := hc k₁ hk₁ y₂ (sk.T₂_le hy₂)
    apply mul_left_cancel (a := k₁)
    calc k₁ * (k₂ * y₂) = (k₁ * k₂) * y₂ := by rw [mul_assoc]
      _ = y₂ * (k₁ * k₂) := h1
      _ = (y₂ * k₁) * k₂ := by rw [mul_assoc]
      _ = (k₁ * y₂) * k₂ := by rw [h2]
      _ = k₁ * (y₂ * k₂) := by rw [mul_assoc]
  have hk₁T : k₁ ∈ T₁ := sk.T₁_cent y₁ hy₁ hy₁y k₁ hk₁ hk₁y
  have hk₂T : k₂ ∈ T₂ := sk.T₂_cent y₂ hy₂ hy₂y k₂ hk₂ hk₂y
  have e : w * s * w⁻¹ = k₁ * k₂ * s := by rw [← hdk]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (skel_T₁_le_H hk₁T) (skel_T₂_le_H hk₂T)) skel_s_mem_H

theorem MixSkel.w₁_normH (hq₁ : 3 ≤ c₁) (hq₂ : 3 ≤ c₂) (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hKC : K₁ ⊔ K₂ ≤ C₁) (hidx : (K₁ ⊔ K₂).relIndex C₁ = 2) :
    ∀ h ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s, w₁ * h * w₁⁻¹ ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s := by
  refine skel_conj_mem_sup (fun a ha => ?_) (fun b hb => ?_) ?_
  · rw [sk.w₁_inv a ha]
    exact skel_T₁_le_H (T₁.inv_mem ha)
  · rw [sk.w₁_conj_T₂ hc hb]
    exact skel_T₂_le_H hb
  · refine sk.conj_s_mem hq₁ hq₂ hc hKC hidx (Subgroup.mem_sup_left sk.w₁_mem) (fun y hy => ?_)
      (fun y hy => ?_)
    · rw [sk.w₁_inv' hy]
      exact T₁.inv_mem hy
    · rw [sk.w₁_conj_T₂' hc hy]
      exact hy

theorem MixSkel.w₂_normH (hq₁ : 3 ≤ c₁) (hq₂ : 3 ≤ c₂) (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hKC : K₁ ⊔ K₂ ≤ C₁) (hidx : (K₁ ⊔ K₂).relIndex C₁ = 2) :
    ∀ h ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s, w₂ * h * w₂⁻¹ ∈ T₁ ⊔ T₂ ⊔ Subgroup.zpowers s := by
  refine skel_conj_mem_sup (fun a ha => ?_) (fun b hb => ?_) ?_
  · rw [sk.w₂_conj_T₁ hc ha]
    exact skel_T₁_le_H ha
  · rw [sk.w₂_inv b hb]
    exact skel_T₂_le_H (T₂.inv_mem hb)
  · refine sk.conj_s_mem hq₁ hq₂ hc hKC hidx (Subgroup.mem_sup_right sk.w₂_mem) (fun y hy => ?_)
      (fun y hy => ?_)
    · rw [sk.w₂_conj_T₁' hc hy]
      exact hy
    · rw [sk.w₂_inv' hy]
      exact T₂.inv_mem hy

theorem MixSkel.mem_T₁_of_comm (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {x : G} (hx : x ∈ K₁)
    (h : x * (x₁ * x₂) = (x₁ * x₂) * x) : x ∈ T₁ := by
  have hx₂ : x * x₂ = x₂ * x := hc x hx x₂ (sk.T₂_le sk.x₂_mem)
  have h1 : x * x₁ = x₁ * x := by
    apply mul_right_cancel (b := x₂)
    calc x * x₁ * x₂ = x * (x₁ * x₂) := by rw [mul_assoc]
      _ = (x₁ * x₂) * x := h
      _ = x₁ * (x₂ * x) := by rw [mul_assoc]
      _ = x₁ * (x * x₂) := by rw [hx₂]
      _ = x₁ * x * x₂ := by rw [mul_assoc]
  exact (sk.T₁_iff x hx).2 h1

theorem MixSkel.mem_T₂_of_comm (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {x : G} (hx : x ∈ K₂)
    (h : x * (x₁ * x₂) = (x₁ * x₂) * x) : x ∈ T₂ := by
  have hx₁ : x₁ * x = x * x₁ := hc x₁ (sk.T₁_le sk.x₁_mem) x hx
  have h1 : x * x₂ = x₂ * x := by
    apply mul_left_cancel (a := x₁)
    calc x₁ * (x * x₂) = x₁ * x * x₂ := by rw [mul_assoc]
      _ = x * x₁ * x₂ := by rw [hx₁]
      _ = x * (x₁ * x₂) := by rw [mul_assoc]
      _ = (x₁ * x₂) * x := h
      _ = x₁ * (x₂ * x) := by rw [mul_assoc]
  exact (sk.T₂_iff x hx).2 h1

theorem MixSkel.H_inf_K₁ (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    (T₁ ⊔ T₂ ⊔ Subgroup.zpowers s) ⊓ K₁ = T₁ :=
  le_antisymm
    (fun _ hx => sk.mem_T₁_of_comm hc hx.2 (sk.H_comm hc _ hx.1 _ sk.u_mem_H))
    (fun _ hx => ⟨skel_T₁_le_H hx, sk.T₁_le hx⟩)

theorem MixSkel.H_inf_K₂ (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    (T₁ ⊔ T₂ ⊔ Subgroup.zpowers s) ⊓ K₂ = T₂ :=
  le_antisymm
    (fun _ hx => sk.mem_T₂_of_comm hc hx.2 (sk.H_comm hc _ hx.1 _ sk.u_mem_H))
    (fun _ hx => ⟨skel_T₂_le_H hx, sk.T₂_le hx⟩)

theorem MixSkel.H_idx (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    (((T₁ ⊔ T₂ ⊔ Subgroup.zpowers s) ⊓ K₁) ⊔ ((T₁ ⊔ T₂ ⊔ Subgroup.zpowers s) ⊓ K₂)).relIndex
      (T₁ ⊔ T₂ ⊔ Subgroup.zpowers s) = 2 := by
  rw [sk.H_inf_K₁ hc, sk.H_inf_K₂ hc]
  refine skel_relIndex_two skel_s_mem_H (fun h => sk.s_not_mem (sup_le_sup sk.T₁_le sk.T₂_le h))
    sk.s_sq ?_
  intro x hx
  obtain ⟨a, ha, b, hb, k, rfl⟩ := sk.exists_decomp hc hx
  exact skel_zpow_cases sk.s_sq (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right hb)) k

theorem MixSkel.x₁_not_mem_K₂ (hzz : z * z = 1) (hzne : z ≠ 1)
    (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z) : x₁ ∉ K₂ := by
  intro h
  have e := sk.x₁_sq
  rcases t2C_zpowers_cases hzz (hinter ⟨sk.T₁_le sk.x₁_mem, h⟩) with h1 | h1
  · rw [h1, one_mul] at e
    exact hzne e.symm
  · rw [h1] at e
    exact hzne (e.symm.trans hzz)

end Skel

section Cfg

variable {G : Type} [Group G]

theorem MixSkel.toCh6MixCfg {C₁ : Subgroup G} {q₁ q₂ : ℕ} {z : G} {K₁ K₂ T₁ T₂ : Subgroup G}
    {x₁ x₂ w₁ w₂ s : G} (sk : MixSkel C₁ (q₁ + 1) (q₂ - 1) z K₁ K₂ T₁ T₂ x₁ x₂ w₁ w₂ s)
    (hq₁ : 5 ≤ q₁) (hq₂ : 4 ≤ q₂) (hzz : z * z = 1) (hzne : z ≠ 1)
    (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z)
    (hCz : ∀ x ∈ C₁, x * z = z * x) (hKC : K₁ ⊔ K₂ ≤ C₁)
    (hN₁ : ∀ c ∈ C₁, ∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) (hN₂ : ∀ c ∈ C₁, ∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂)
    (hidx : (K₁ ⊔ K₂).relIndex C₁ = 2) :
    Ch6MixCfg C₁ q₁ q₂ z (x₁ * x₂) K₁ K₂ (T₁ ⊔ T₂ ⊔ Subgroup.zpowers s) w₁ w₂ := by
  have hq₁3 : 3 ≤ q₁ + 1 := by omega
  have hq₂3 : 3 ≤ q₂ - 1 := by omega
  have hx₁K₂ : x₁ ∉ K₂ := sk.x₁_not_mem_K₂ hzz hzne hinter
  have hx₁₂ : x₁ * x₂ = x₂ * x₁ := hc x₁ (sk.T₁_le sk.x₁_mem) x₂ (sk.T₂_le sk.x₂_mem)
  have huK : x₁ * x₂ ∈ K₁ ⊔ K₂ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (sk.T₁_le sk.x₁_mem))
      (Subgroup.mem_sup_right (sk.T₂_le sk.x₂_mem))
  have hzx₂ : x₂ * z = z * x₂ := hCz x₂ (hKC (Subgroup.mem_sup_right (sk.T₂_le sk.x₂_mem)))
  have hw₁x₂ : w₁ * x₂ * w₁⁻¹ = x₂ := by
    rw [hc w₁ sk.w₁_mem x₂ (sk.T₂_le sk.x₂_mem)]
    group
  have hw₂x₁ : w₂ * x₁ * w₂⁻¹ = x₁ := by
    rw [← hc x₁ (sk.T₁_le sk.x₁_mem) w₂ sk.w₂_mem]
    group
  refine
    { zz := hzz, z_ne := hzne, uu := ?_, u_ne := ?_, zu_ne := ?_, zu_comm := ?_, K_comm := hc,
      K_inter := hinter, C_comm := hCz, K_le_C := hKC, C_norm₁ := hN₁, C_norm₂ := hN₂,
      C_idx := hidx, H_comm := sk.H_comm hc, z_mem_H := sk.z_mem_H, u_mem_H := sk.u_mem_H,
      H_le_C := ?_, H_not_le_K := fun hle => sk.s_not_mem (hle skel_s_mem_H),
      H₁_iff := fun x hx => ⟨fun hxH => sk.H_comm hc x hxH _ sk.u_mem_H,
        fun h => skel_T₁_le_H (sk.mem_T₁_of_comm hc hx h)⟩,
      H₂_iff := fun x hx => ⟨fun hxH => sk.H_comm hc x hxH _ sk.u_mem_H,
        fun h => skel_T₂_le_H (sk.mem_T₂_of_comm hc hx h)⟩,
      w₁_mem := sk.w₁_mem, w₂_mem := sk.w₂_mem, w₁_sq := sk.w₁_sq, w₂_sq := sk.w₂_sq,
      w₁_u := ?_, w₂_u := ?_, w₁_normH := sk.w₁_normH hq₁3 hq₂3 hc hKC hidx,
      w₂_normH := sk.w₂_normH hq₁3 hq₂3 hc hKC hidx, w₀_inv := sk.w₀_inv hc, w₀_not_mem := ?_,
      H₁_cyc := ?_, H₂_cyc := ?_, H₁_card := ?_, H₂_card := ?_, H_idx := sk.H_idx hc,
      H₁_cent := ?_ }
  · calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [hx₁₂]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [sk.x₁_sq, sk.x₂_sq, hzz]
  · intro h
    apply hx₁K₂
    rw [eq_inv_of_mul_eq_one_left h]
    exact K₂.inv_mem (sk.T₂_le sk.x₂_mem)
  · intro h
    apply hx₁K₂
    have : x₁ = x₂ := mul_left_cancel (sk.x₁_sq.trans h)
    rw [this]
    exact sk.T₂_le sk.x₂_mem
  · exact (hCz _ (hKC huK)).symm
  · exact sup_le (sup_le (sk.T₁_le.trans (le_sup_left.trans hKC))
      (sk.T₂_le.trans (le_sup_right.trans hKC))) (Subgroup.zpowers_le.2 sk.s_mem)
  · calc w₁ * (x₁ * x₂) * w₁⁻¹ = (w₁ * x₁ * w₁⁻¹) * (w₁ * x₂ * w₁⁻¹) := by group
      _ = (x₁ * z) * x₂ := by rw [sk.w₁_x, hw₁x₂]
      _ = x₁ * (x₂ * z) := by rw [mul_assoc, hzx₂]
      _ = (x₁ * x₂) * z := by rw [mul_assoc]
  · calc w₂ * (x₁ * x₂) * w₂⁻¹ = (w₂ * x₁ * w₂⁻¹) * (w₂ * x₂ * w₂⁻¹) := by group
      _ = x₁ * (x₂ * z) := by rw [hw₂x₁, sk.w₂_x]
      _ = (x₁ * x₂) * z := by rw [mul_assoc]
  · refine t2C_w0_not_mem (K := K₁) (sk.H_comm hc) (sk.w₀_inv hc) ?_ ?_
    · rw [sk.H_inf_K₁ hc]
      exact sk.T₁_cyc
    · rw [sk.H_inf_K₁ hc, sk.T₁_card]
      exact hq₁3
  · rw [sk.H_inf_K₁ hc]
    exact sk.T₁_cyc
  · rw [sk.H_inf_K₂ hc]
    exact sk.T₂_cyc
  · rw [sk.H_inf_K₁ hc]
    exact sk.T₁_card
  · rw [sk.H_inf_K₂ hc]
    exact sk.T₂_card
  · intro y hy hyy d hd hdy
    rw [sk.H_inf_K₁ hc] at hy
    exact skel_T₁_le_H (sk.T₁_cent y hy hyy d hd hdy)

end Cfg

end CFSG.GH74.GLS.Stage4.Rest
