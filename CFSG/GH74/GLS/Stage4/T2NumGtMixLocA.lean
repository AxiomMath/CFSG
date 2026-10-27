module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocDefs
public import CFSG.GH74.GLS.Stage4.T2NegCfgOne

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.T2
open scoped Pointwise commutatorElement

section CaseA

variable {G : Type} [Group G] [Finite G]

theorem ch6MixCfg_of_t_factors {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {Hd₁ Hd₂ : Subgroup G} {w₁ w₂ : G}
    (hHd₁K : Hd₁ ≤ K₁) (hcyc₁ : IsCyclic ↥Hd₁) (hcard₁ : Nat.card ↥Hd₁ = q₁ + 1)
    (hiff₁ : ∀ x ∈ K₁, x ∈ Hd₁ ↔ x * t = t * x) (hw₁K : w₁ ∈ K₁) (hw₁sq : w₁ * w₁ = z)
    (hw₁t : t * w₁ * t⁻¹ = w₁⁻¹) (hw₁inv : ∀ x ∈ Hd₁, w₁ * x * w₁⁻¹ = x⁻¹)
    (hcent₁ : ∀ y ∈ Hd₁, y * y ≠ 1 → ∀ d ∈ K₁, d * y = y * d → d ∈ Hd₁)
    (hHd₂K : Hd₂ ≤ K₂) (hcyc₂ : IsCyclic ↥Hd₂) (hcard₂ : Nat.card ↥Hd₂ = q₂ - 1)
    (hiff₂ : ∀ x ∈ K₂, x ∈ Hd₂ ↔ x * t = t * x) (hw₂K : w₂ ∈ K₂) (hw₂sq : w₂ * w₂ = z)
    (hw₂t : t * w₂ * t⁻¹ = w₂⁻¹) (hw₂inv : ∀ x ∈ Hd₂, w₂ * x * w₂⁻¹ = x⁻¹) :
    Ch6MixCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q₁ q₂ z t K₁ K₂
        (Hd₁ ⊔ Hd₂ ⊔ Subgroup.zpowers t) w₁ w₂ ∧
      (Hd₁ ⊔ Hd₂ ⊔ Subgroup.zpowers t) ⊓ K₂ = Hd₂ := by
  have h5 : 5 ≤ q₁ := hSet.five
  have hzz : z * z = 1 := t2C_zz hSet
  have htt : t * t = 1 := hRem.sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htK := t2B_t_notin hSet hRem
  have hHd₁c := t2B_cyclic_comm Hd₁ hcyc₁
  have hHd₂c := t2B_cyclic_comm Hd₂ hcyc₂
  have hHd₁₂ : ∀ x ∈ Hd₁, ∀ y ∈ Hd₂, x * y = y * x := fun x hx y hy =>
    hSet.comm x (hHd₁K hx) y (hHd₂K hy)
  have hHd₁t : ∀ x ∈ Hd₁, x * t = t * x := fun x hx => (hiff₁ x (hHd₁K hx)).1 hx
  have hHd₂t : ∀ x ∈ Hd₂, x * t = t * x := fun x hx => (hiff₂ x (hHd₂K hx)).1 hx
  have hAc : ∀ x ∈ Hd₁ ⊔ Hd₂, ∀ y ∈ Hd₁ ⊔ Hd₂, x * y = y * x :=
    t2B_sup_comm hHd₁c hHd₂c hHd₁₂
  have hAt : ∀ x ∈ Hd₁ ⊔ Hd₂, x * t = t * x := by
    have : Hd₁ ⊔ Hd₂ ≤ centralizer ({t} : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hHd₁t x hx))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hHd₂t x hx))
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (this hx)
  have hZc : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self t m n).eq
  have hAZ : ∀ x ∈ Hd₁ ⊔ Hd₂, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hxt : Commute x t := hAt x hx
    exact (hxt.zpow_right n).eq
  set H : Subgroup G := (Hd₁ ⊔ Hd₂) ⊔ Subgroup.zpowers t with hHdef
  have hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := t2B_sup_comm hAc hZc hAZ
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHd₁H : Hd₁ ≤ H := le_sup_left.trans le_sup_left
  have hHd₂H : Hd₂ ≤ H := le_sup_right.trans le_sup_left
  have hzH : z ∈ H :=
    hHd₁H ((hiff₁ z hSet.z_mem₁).2 hRem.comm_z.symm)
  have hform : ∀ x ∈ H, ∃ h₁ ∈ Hd₁, ∃ h₂ ∈ Hd₂, x = h₁ * h₂ ∨ x = h₁ * h₂ * t := by
    intro x hx
    obtain ⟨p, hp, s, hs, rfl⟩ := (mem_sup_iff_of_comm hAZ x).1 hx
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := (mem_sup_iff_of_comm hHd₁₂ p).1 hp
    rcases t2C_zpowers_cases htt hs with rfl | rfl
    · exact ⟨h₁, hh₁, h₂, hh₂, Or.inl (mul_one _)⟩
    · exact ⟨h₁, hh₁, h₂, hh₂, Or.inr rfl⟩
  have hHK₁ : H ⊓ K₁ = Hd₁ :=
    le_antisymm (fun x hx => (hiff₁ x hx.2).2 (hHc x hx.1 t htH))
      (fun x hx => ⟨hHd₁H hx, hHd₁K hx⟩)
  have hHK₂ : H ⊓ K₂ = Hd₂ :=
    le_antisymm (fun x hx => (hiff₂ x hx.2).2 (hHc x hx.1 t htH))
      (fun x hx => ⟨hHd₂H hx, hHd₂K hx⟩)
  have hw₁t' : t * w₁ * t = w₁⁻¹ := by rw [hti] at hw₁t; exact hw₁t
  have hw₂t' : t * w₂ * t = w₂⁻¹ := by rw [hti] at hw₂t; exact hw₂t
  have hw₁z : w₁ * z = z * w₁ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_left hw₁K))
  have hw₂z : w₂ * z = z * w₂ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_right hw₂K))
  have hw₁tz : w₁ * t * w₁⁻¹ = t * z := by
    have h1 : w₁ * t = t * w₁⁻¹ := by
      calc w₁ * t = (t * t) * w₁ * t := by rw [htt, one_mul]
        _ = t * (t * w₁ * t) := by group
        _ = t * w₁⁻¹ := by rw [hw₁t']
    calc w₁ * t * w₁⁻¹ = t * (w₁⁻¹ * w₁⁻¹) := by rw [h1]; group
      _ = t * (w₁ * w₁)⁻¹ := by group
      _ = t * z := by rw [hw₁sq]; rw [inv_eq_of_mul_eq_one_right hzz]
  have hw₂tz : w₂ * t * w₂⁻¹ = t * z := by
    have h1 : w₂ * t = t * w₂⁻¹ := by
      calc w₂ * t = (t * t) * w₂ * t := by rw [htt, one_mul]
        _ = t * (t * w₂ * t) := by group
        _ = t * w₂⁻¹ := by rw [hw₂t']
    calc w₂ * t * w₂⁻¹ = t * (w₂⁻¹ * w₂⁻¹) := by rw [h1]; group
      _ = t * (w₂ * w₂)⁻¹ := by group
      _ = t * z := by rw [hw₂sq]; rw [inv_eq_of_mul_eq_one_right hzz]
  have hc₁₁ : ∀ x ∈ Hd₁, w₁ * x * w₁⁻¹ = x⁻¹ := hw₁inv
  have hc₂₂ : ∀ x ∈ Hd₂, w₂ * x * w₂⁻¹ = x⁻¹ := hw₂inv
  have hc₁₂ : ∀ y ∈ Hd₂, w₁ * y * w₁⁻¹ = y := by
    intro y hy
    rw [hSet.comm w₁ hw₁K y (hHd₂K hy)]; group
  have hc₂₁ : ∀ x ∈ Hd₁, w₂ * x * w₂⁻¹ = x := by
    intro x hx
    rw [(hSet.comm x (hHd₁K hx) w₂ hw₂K).symm]; group
  have hinv2 : ∀ h₁ ∈ Hd₁, ∀ h₂ ∈ Hd₂, (h₁ * h₂)⁻¹ = h₁⁻¹ * h₂⁻¹ := by
    intro h₁ hh₁ h₂ hh₂
    have := hHd₁₂ h₁⁻¹ (Hd₁.inv_mem hh₁) h₂⁻¹ (Hd₂.inv_mem hh₂)
    calc (h₁ * h₂)⁻¹ = h₂⁻¹ * h₁⁻¹ := by group
      _ = h₁⁻¹ * h₂⁻¹ := this.symm
  have hinv3 : ∀ h₁ ∈ Hd₁, ∀ h₂ ∈ Hd₂, (h₁ * h₂ * t)⁻¹ = h₁⁻¹ * h₂⁻¹ * t := by
    intro h₁ hh₁ h₂ hh₂
    have hp : (h₁ * h₂)⁻¹ ∈ Hd₁ ⊔ Hd₂ :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₁) (Subgroup.mem_sup_right hh₂))
    have := hAt _ hp
    calc (h₁ * h₂ * t)⁻¹ = t⁻¹ * (h₁ * h₂)⁻¹ := by group
      _ = t * (h₁ * h₂)⁻¹ := by rw [hti]
      _ = (h₁ * h₂)⁻¹ * t := this.symm
      _ = h₁⁻¹ * h₂⁻¹ * t := by rw [hinv2 h₁ hh₁ h₂ hh₂]
  have hw₀inv : ∀ x ∈ H, (w₁ * w₂) * x * (w₁ * w₂)⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have e1 : (w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹ = h₁⁻¹ := by
      calc (w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * h₁ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * h₁ * w₁⁻¹ := by rw [hc₂₁ h₁ hh₁]
        _ = h₁⁻¹ := hc₁₁ h₁ hh₁
    have e2 : (w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹ = h₂⁻¹ := by
      calc (w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹ = w₁ * (w₂ * h₂ * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * h₂⁻¹ * w₁⁻¹ := by rw [hc₂₂ h₂ hh₂]
        _ = h₂⁻¹ := hc₁₂ h₂⁻¹ (Hd₂.inv_mem hh₂)
    have e3 : (w₁ * w₂) * t * (w₁ * w₂)⁻¹ = t := by
      calc (w₁ * w₂) * t * (w₁ * w₂)⁻¹ = w₁ * (w₂ * t * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (t * z) * w₁⁻¹ := by rw [hw₂tz]
        _ = (w₁ * t * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
        _ = (t * z) * z := by
            rw [hw₁tz, show w₁ * z * w₁⁻¹ = z by rw [hw₁z]; group]
        _ = t := by rw [mul_assoc, hzz, mul_one]
    rcases hxe with rfl | rfl
    · rw [hinv2 h₁ hh₁ h₂ hh₂]
      calc (w₁ * w₂) * (h₁ * h₂) * (w₁ * w₂)⁻¹
          = ((w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹) * ((w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹) := by group
        _ = h₁⁻¹ * h₂⁻¹ := by rw [e1, e2]
    · rw [hinv3 h₁ hh₁ h₂ hh₂]
      calc (w₁ * w₂) * (h₁ * h₂ * t) * (w₁ * w₂)⁻¹
          = ((w₁ * w₂) * h₁ * (w₁ * w₂)⁻¹) * ((w₁ * w₂) * h₂ * (w₁ * w₂)⁻¹) *
              ((w₁ * w₂) * t * (w₁ * w₂)⁻¹) := by group
        _ = h₁⁻¹ * h₂⁻¹ * t := by rw [e1, e2, e3]
  have hw₁norm : ∀ x ∈ H, w₁ * x * w₁⁻¹ ∈ H := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hH1 : h₁⁻¹ ∈ H := H.inv_mem (hHd₁H hh₁)
    have hH2 : h₂ ∈ H := hHd₂H hh₂
    rcases hxe with rfl | rfl
    · have : w₁ * (h₁ * h₂) * w₁⁻¹ = h₁⁻¹ * h₂ := by
        calc w₁ * (h₁ * h₂) * w₁⁻¹ = (w₁ * h₁ * w₁⁻¹) * (w₁ * h₂ * w₁⁻¹) := by group
          _ = h₁⁻¹ * h₂ := by rw [hc₁₁ h₁ hh₁, hc₁₂ h₂ hh₂]
      rw [this]; exact H.mul_mem hH1 hH2
    · have : w₁ * (h₁ * h₂ * t) * w₁⁻¹ = h₁⁻¹ * h₂ * (t * z) := by
        calc w₁ * (h₁ * h₂ * t) * w₁⁻¹
            = (w₁ * h₁ * w₁⁻¹) * (w₁ * h₂ * w₁⁻¹) * (w₁ * t * w₁⁻¹) := by group
          _ = h₁⁻¹ * h₂ * (t * z) := by rw [hc₁₁ h₁ hh₁, hc₁₂ h₂ hh₂, hw₁tz]
      rw [this]; exact H.mul_mem (H.mul_mem hH1 hH2) (H.mul_mem htH hzH)
  have hw₂norm : ∀ x ∈ H, w₂ * x * w₂⁻¹ ∈ H := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hH1 : h₁ ∈ H := hHd₁H hh₁
    have hH2 : h₂⁻¹ ∈ H := H.inv_mem (hHd₂H hh₂)
    rcases hxe with rfl | rfl
    · have : w₂ * (h₁ * h₂) * w₂⁻¹ = h₁ * h₂⁻¹ := by
        calc w₂ * (h₁ * h₂) * w₂⁻¹ = (w₂ * h₁ * w₂⁻¹) * (w₂ * h₂ * w₂⁻¹) := by group
          _ = h₁ * h₂⁻¹ := by rw [hc₂₁ h₁ hh₁, hc₂₂ h₂ hh₂]
      rw [this]; exact H.mul_mem hH1 hH2
    · have : w₂ * (h₁ * h₂ * t) * w₂⁻¹ = h₁ * h₂⁻¹ * (t * z) := by
        calc w₂ * (h₁ * h₂ * t) * w₂⁻¹
            = (w₂ * h₁ * w₂⁻¹) * (w₂ * h₂ * w₂⁻¹) * (w₂ * t * w₂⁻¹) := by group
          _ = h₁ * h₂⁻¹ * (t * z) := by rw [hc₂₁ h₁ hh₁, hc₂₂ h₂ hh₂, hw₂tz]
      rw [this]; exact H.mul_mem (H.mul_mem hH1 hH2) (H.mul_mem htH hzH)
  have hw₀notin : w₁ * w₂ ∉ H := by
    refine t2C_w0_not_mem (K := K₁) hHc hw₀inv ?_ ?_
    · rw [hHK₁]; exact hcyc₁
    · rw [hHK₁, hcard₁]; omega
  have hKC : K₁ ⊔ K₂ ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := hSet.le_residual
  have htC : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hRem.gen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHle : H ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
    sup_le (sup_le (hHd₁K.trans (le_sup_left.trans hKC)) (hHd₂K.trans (le_sup_right.trans hKC)))
      (Subgroup.zpowers_le.2 htC)
  have hC₁le : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ centralizer ({z} : Set G) :=
    Subgroup.map_subtype_le _
  have hformA : ∀ x ∈ H, x ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂) ∨ ∃ y ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂), x = y * t := by
    intro x hx
    obtain ⟨h₁, hh₁, h₂, hh₂, hxe⟩ := hform x hx
    have hp : h₁ * h₂ ∈ (H ⊓ K₁) ⊔ (H ⊓ K₂) := by
      rw [hHK₁, hHK₂]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₁) (Subgroup.mem_sup_right hh₂)
    rcases hxe with rfl | rfl
    · exact Or.inl hp
    · exact Or.inr ⟨h₁ * h₂, hp, rfl⟩
  refine ⟨?_, hHK₂⟩
  refine
    { zz := hzz, z_ne := t2C_z_ne hSet, uu := htt,
      u_ne := fun h1 => htK (h1 ▸ (K₁ ⊔ K₂).one_mem),
      zu_ne := fun h1 => htK (h1 ▸ Subgroup.mem_sup_left hSet.z_mem₁),
      zu_comm := hRem.comm_z.symm, K_comm := hSet.comm, K_inter := hSet.inter_eq.le,
      C_comm := fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hC₁le hx),
      K_le_C := hKC,
      C_norm₁ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).1 c hc,
      C_norm₂ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).2 c hc,
      C_idx := hSet.index_two, H_comm := hHc, z_mem_H := hzH, u_mem_H := htH,
      H_le_C := hHle, H_not_le_K := fun hle => htK (hle htH),
      H₁_iff := ?_, H₂_iff := ?_, w₁_mem := hw₁K, w₂_mem := hw₂K, w₁_sq := hw₁sq,
      w₂_sq := hw₂sq, w₁_u := hw₁tz, w₂_u := hw₂tz, w₁_normH := hw₁norm,
      w₂_normH := hw₂norm, w₀_inv := hw₀inv, w₀_not_mem := hw₀notin,
      H₁_cyc := ?_, H₂_cyc := ?_, H₁_card := ?_, H₂_card := ?_, H_idx := ?_,
      H₁_cent := fun y hy hyy d hd hdy => hHd₁H (hcent₁ y (hHK₁ ▸ hy) hyy d hd hdy) }
  · intro x hx
    exact ⟨fun hxH => hHc x hxH t htH, fun hxt => hHd₁H ((hiff₁ x hx).2 hxt)⟩
  · intro x hx
    exact ⟨fun hxH => hHc x hxH t htH, fun hxt => hHd₂H ((hiff₂ x hx).2 hxt)⟩
  · rw [hHK₁]; exact hcyc₁
  · rw [hHK₂]; exact hcyc₂
  · rw [hHK₁, hcard₁]
  · rw [hHK₂, hcard₂]
  · have hAle : (H ⊓ K₁) ⊔ (H ⊓ K₂) ≤ K₁ ⊔ K₂ := sup_le_sup inf_le_right inf_le_right
    exact t2N_relIndex_two htH (fun h => htK (hAle h)) htt hformA

theorem mixA_normalizes {F : Type} [Field F] (φ : SL2 F →* G) (t : G) {Hd₁ Hd₂ : Subgroup G}
    {A : Subgroup (SL2 F)} (hHd₁ : ∀ h ∈ Hd₁, ∀ y : SL2 F, h * φ y = φ y * h)
    (hHd₂ : ∀ h ∈ Hd₂, ∀ x ∈ A.map φ, h * x * h⁻¹ ∈ A.map φ)
    (ht : ∀ x ∈ A.map φ, t * x * t⁻¹ ∈ A.map φ) :
    ∀ h ∈ Hd₁ ⊔ Hd₂ ⊔ Subgroup.zpowers t, ∀ x ∈ A.map φ, h * x * h⁻¹ ∈ A.map φ := by
  have h1 : Hd₁ ≤ normalizer ((A.map φ : Subgroup G) : Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
    obtain ⟨a, ha, rfl⟩ := hx
    have : h * φ a * h⁻¹ = φ a := by rw [hHd₁ h hh a]; group
    rw [this]
    exact ⟨a, ha, rfl⟩
  have h2 : Hd₂ ≤ normalizer ((A.map φ : Subgroup G) : Set G) := fun h hh =>
    Subgroup.mem_normalizer_fintype (fun x hx => hHd₂ h hh x hx)
  have h3 : Subgroup.zpowers t ≤ normalizer ((A.map φ : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_normalizer_fintype (fun x hx => ht x hx)
  intro h hh x hx
  exact (Subgroup.mem_normalizer_iff.1 ((sup_le (sup_le h1 h2) h3) hh) x).1 hx

theorem mixCfg_a {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (h1 : q₁ % 4 = 1) (h3 : q₂ % 4 = 3) :
    ∃ (H : Subgroup G) (w₁ w₂ : G) (φ₁ : SL2 F₁ →* G) (φ₂ : SL2 F₂ →* G),
      Ch6MixCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q₁ q₂ z t K₁ K₂ H w₁ w₂ ∧
        Function.Injective φ₁ ∧ φ₁.range = K₁ ∧ MixCoord2 φ₂ z t w₂ K₂ H := by
  have := hSet.finite₁
  have := hSet.finite₂
  have h5 : 5 ≤ q₁ := hSet.five
  have hzord : orderOf z = 2 := hSet.central.1
  have htt : t * t = 1 := hRem.sq
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; omega
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card hodd₁
  have h2₂ : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card hodd₂
  have hq1 : (q₁ : ℤ) ≡ 1 [ZMOD 4] := by unfold Int.ModEq; omega
  have hdd : ((q₁ + 1 : ℕ) : ℤ) = q₁ + 1 := by push_cast; ring
  obtain ⟨e₁, g₁, hns₁, hact₁⟩ := hRem.diag₁
  obtain ⟨e₂, g₂, hns₂, hact₂⟩ := hRem.diag₂
  obtain ⟨Hd₁, w₁, hHd₁K, hcyc₁, hcard₁, hiff₁, hw₁K, hw₁sq, hw₁t, hw₁inv⟩ :=
    t2B_factor hodd₁ h3₁ hzord hSet.z_mem₁ htt e₁ g₁ hns₁ hact₁ 1 (Or.inl rfl)
      (by rw [hSet.card₁]; exact hq1) (q₁ + 1) (by rw [hSet.card₁]; exact hdd)
  have hcent₁ : ∀ y ∈ Hd₁, y * y ≠ 1 → ∀ d ∈ K₁, d * y = y * d → d ∈ Hd₁ :=
    fun y hy hyy d hd hdy =>
      t2N_cent h2₁ hzord hSet.z_mem₁ htt e₁ g₁ hact₁ hiff₁ (hHd₁K hy) hy hyy hd hdy
  obtain ⟨φ₁, hinj₁, hrange₁, -, -, -⟩ := exists_coords0 h2₁ hzord hSet.z_mem₁ htt e₁ g₁ hact₁
  obtain ⟨φ₂', inj₂', range₂', z₂', hτ₂', hsq₂'⟩ :=
    exists_coords0 h2₂ hzord hSet.z_mem₂ htt e₂ g₂ hact₂
  have hF₂ : Nat.card F₂ % 4 = 3 := by rw [hSet.card₂]; exact h3
  obtain ⟨φ₂, hinj₂, hrange₂, hneg₂, hτ₂⟩ :=
    coords_B h2₂ hF₂ φ₂' inj₂' range₂' z₂' g₂ hns₂ hτ₂' hsq₂'
  have hmemK₂ : ∀ y : SL2 F₂, φ₂ y ∈ K₂ := fun y => hrange₂ ▸ ⟨y, rfl⟩
  have hcentr₂ : ∀ y : SL2 F₂, t * φ₂ y = φ₂ y * t ↔ y ∈ tSub F₂ := by
    intro y
    constructor
    · intro hc
      have h1' := hτ₂ y
      have h2' : t * φ₂ y * t⁻¹ = φ₂ y := by rw [hc]; group
      rw [h2'] at h1'
      exact centralizer_dNeg h2₂ y (hinj₂ h1'.symm)
    · intro hy
      have h1' := hτ₂ y
      have h3' : slConj (dNeg F₂) y = y := slConj_diag_tSub 1 (-1) y hy
      rw [h3'] at h1'
      exact mul_inv_eq_iff_eq_mul.1 h1'
  have hiff₂ : ∀ x ∈ K₂, x ∈ (tSub F₂).map φ₂ ↔ x * t = t * x := by
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ φ₂.range := hrange₂ ▸ hx
    rw [Subgroup.mem_map_iff_mem hinj₂, ← hcentr₂ y]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hHd₂K : (tSub F₂).map φ₂ ≤ K₂ := by
    rintro _ ⟨y, -, rfl⟩
    exact hmemK₂ y
  have hcyc₂ : IsCyclic ↥((tSub F₂).map φ₂) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ hinj₂)).1 isCyclic_tSub
  have hcard₂ : Nat.card ↥((tSub F₂).map φ₂) = q₂ - 1 := by
    rw [card_map_eq _ φ₂ hinj₂, card_tSub, hSet.card₂]
  have hwconj₂ : ∀ x : SL2 F₂, φ₂ (sl2W F₂) * φ₂ x * (φ₂ (sl2W F₂))⁻¹ =
      φ₂ (sl2W F₂ * x * (sl2W F₂)⁻¹) := fun x => by simp [map_mul, map_inv]
  have hw₂K : φ₂ (sl2W F₂) ∈ K₂ := hmemK₂ _
  have hw₂sq : φ₂ (sl2W F₂) * φ₂ (sl2W F₂) = z := by rw [← map_mul, sl2W_sq, hneg₂]
  have hw₂t : t * φ₂ (sl2W F₂) * t⁻¹ = (φ₂ (sl2W F₂))⁻¹ := by
    rw [hτ₂, slConj_dNeg_W, map_inv]
  have hw₂inv : ∀ x ∈ (tSub F₂).map φ₂, φ₂ (sl2W F₂) * x * (φ₂ (sl2W F₂))⁻¹ = x⁻¹ := fun x hx =>
    map_conj_inv φ₂ _ (fun x => sl2W F₂ * x * (sl2W F₂)⁻¹) hwconj₂ sl2W_inv_tSub x hx
  obtain ⟨cfg, hHK₂⟩ := ch6MixCfg_of_t_factors hSet hRem hHd₁K hcyc₁ hcard₁ hiff₁ hw₁K hw₁sq hw₁t
    hw₁inv hcent₁ hHd₂K hcyc₂ hcard₂ hiff₂ hw₂K hw₂sq hw₂t hw₂inv
  have hHd₁c : ∀ h ∈ Hd₁, ∀ y : SL2 F₂, h * φ₂ y = φ₂ y * h := fun h hh y =>
    hSet.comm h (hHd₁K hh) _ (hmemK₂ y)
  refine ⟨Hd₁ ⊔ (tSub F₂).map φ₂ ⊔ Subgroup.zpowers t, w₁, φ₂ (sl2W F₂), φ₁, φ₂, cfg, hinj₁,
    hrange₁, hinj₂, hrange₂, hneg₂, rfl, hHK₂, ?_, ?_, hτ₂⟩
  · refine mixA_normalizes φ₂ t hHd₁c ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨d * a * d⁻¹, tSub_normalizes_uSub d hd a ha, by simp [map_mul, map_inv]⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a⁻¹, (uSub F₂).inv_mem ha, by rw [hτ₂, slConj_dNeg_uSub a ha]⟩
  · refine mixA_normalizes φ₂ t hHd₁c ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨d * a * d⁻¹, tSub_normalizes_lSub d hd a ha, by simp [map_mul, map_inv]⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a⁻¹, (lSub F₂).inv_mem ha, by rw [hτ₂, slConj_dNeg_lSub a ha]⟩

end CaseA

end CFSG.GH74.GLS.Stage4.Rest
