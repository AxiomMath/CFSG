module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Defs
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Part

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.L4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local.P27.Psp4

variable {G : Type} [Group G] {S P₁ P₂ : Subgroup G} {z t w : G} {a : ℕ}

namespace DataL4

variable [Finite G] (h : DataL4 S P₁ P₂ z t w a)

include h

theorem A_coset {r : G} (hr : r ∈ P₁ ⊔ P₂) : (r * t * r⁻¹) * t ∈ P₁ ⊔ P₂ := by
  have e : r * t * r⁻¹ * t = r * (t * r⁻¹ * t⁻¹) := by rw [h.t_inv']; simp only [mul_assoc]
  rw [e]
  exact mul_mem hr (h.t_conj_R (inv_mem hr))

theorem C_coset {r : G} (hr : r ∈ P₁ ⊔ P₂) : (r * (t * w) * r⁻¹) * (t * w) ∈ P₁ ⊔ P₂ := by
  have e : r * (t * w) * r⁻¹ * (t * w) = r * (t * (w * r⁻¹ * w⁻¹) * t⁻¹) := by
    calc r * (t * w) * r⁻¹ * (t * w) = r * ((t * w) * r⁻¹ * (t * w)) := by simp only [mul_assoc]
      _ = r * ((t * w) * r⁻¹ * (t * w)⁻¹) := by rw [h.tw_inv']
      _ = r * (t * (w * r⁻¹ * w⁻¹) * t⁻¹) := by group
  rw [e]
  exact mul_mem hr (h.t_conj_R (h.w_conj_R (inv_mem hr)))

theorem Az_coset {r : G} (hr : r ∈ P₁ ⊔ P₂) : (r * (t * z) * r⁻¹) * t ∈ P₁ ⊔ P₂ := by
  rw [h.conj_mul_z (h.R_mem_S hr) h.t_mem, mul_assoc]
  exact mul_mem h.z_mem_R (h.A_coset hr)

theorem Cz_coset {r : G} (hr : r ∈ P₁ ⊔ P₂) : (r * (t * w * z) * r⁻¹) * (t * w) ∈ P₁ ⊔ P₂ := by
  rw [h.conj_mul_z (h.R_mem_S hr) (mul_mem h.t_mem h.w_mem), mul_assoc]
  exact mul_mem h.z_mem_R (h.C_coset hr)

theorem mem_ZcL_R {y : G} (hy : y ∈ P₁ ⊔ P₂) : y ∈ ZcL (P₁ ⊔ P₂) z t w ↔ y = z := by
  constructor
  · rintro (((hz | ⟨r, hr, hyr⟩) | ⟨⟨r, hr, hyr⟩, -⟩) | ⟨r, hr, hyr⟩)
    · exact hz
    · exfalso
      rw [hyr] at hy
      exact h.not_R_Rt hy (h.A_coset hr)
    · exfalso
      have : y * w ∈ P₁ ⊔ P₂ := by rw [hyr, mul_assoc, h.w_inv, mul_one]; exact hr
      exact h.not_R_Rw hy this
    · exfalso
      rw [hyr] at hy
      exact h.not_R_Rtw hy (h.C_coset hr)
  · intro hyz
    exact Or.inl (Or.inl (Or.inl hyz))

theorem mem_XcL_R {y : G} (hy : y ∈ P₁ ⊔ P₂) :
    y ∈ XcL (P₁ ⊔ P₂) z t w ↔ (y * y = 1 ∧ y ≠ 1 ∧ y ≠ z) := by
  constructor
  · rintro ((⟨-, h2⟩ | ⟨r, hr, hyr⟩) | ⟨r, hr, hyr⟩)
    · exact h2
    · exfalso
      rw [hyr] at hy
      exact h.not_R_Rt hy (h.Az_coset hr)
    · exfalso
      rw [hyr] at hy
      exact h.not_R_Rtw hy (h.Cz_coset hr)
  · intro hy'
    exact Or.inl (Or.inl ⟨hy, hy'⟩)

theorem rrt_mem_ZcL_iff {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * t ∈ ZcL (P₁ ⊔ P₂) z t w ↔ p * q = 1 := by
  have hR : rr t p q ∈ P₁ ⊔ P₂ := h.toPsp4.rr_mem_R hp hq
  have hRt : rr t p q * t * t ∈ P₁ ⊔ P₂ := by rw [mul_assoc, h.t_inv, mul_one]; exact hR
  rw [← h.toPsp4.rrt_mem_Zc_iff hp hq]
  constructor
  · rintro (((hZ) | ⟨⟨r, hr, hyr⟩, -⟩) | ⟨r, hr, hyr⟩)
    · exact hZ
    · exfalso
      have : (rr t p q * t) * w ∈ P₁ ⊔ P₂ := by rw [hyr, mul_assoc, h.w_inv, mul_one]; exact hr
      exact h.not_Rt_Rw hRt this
    · exfalso
      have hh : (rr t p q * t) * (t * w) ∈ P₁ ⊔ P₂ := by rw [hyr]; exact h.C_coset hr
      exact h.not_Rt_Rtw hRt hh
  · intro hZ
    exact Or.inl (Or.inl hZ)

theorem rrt_mem_XcL_iff {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * t ∈ XcL (P₁ ⊔ P₂) z t w ↔ p * q = z := by
  have hR : rr t p q ∈ P₁ ⊔ P₂ := h.toPsp4.rr_mem_R hp hq
  have hRt : rr t p q * t * t ∈ P₁ ⊔ P₂ := by rw [mul_assoc, h.t_inv, mul_one]; exact hR
  rw [← h.toPsp4.rrt_mem_Xc_iff hp hq]
  constructor
  · rintro ((hX) | ⟨r, hr, hyr⟩)
    · exact hX
    · exfalso
      have hh : (rr t p q * t) * (t * w) ∈ P₁ ⊔ P₂ := by rw [hyr]; exact h.Cz_coset hr
      exact h.not_Rt_Rtw hRt hh
  · intro hX
    exact Or.inl hX

omit [Finite G] in
theorem mem_ZcL_Rw {y : G} (hy : y * w ∈ P₁ ⊔ P₂) (hy2 : y * y = 1) : y ∈ ZcL (P₁ ⊔ P₂) z t w :=
  Or.inl (Or.inr ⟨⟨y * w, hy, by rw [mul_assoc, h.w_inv, mul_one]⟩, hy2⟩)

theorem not_mem_XcL_Rw {y : G} (hy : y * w ∈ P₁ ⊔ P₂) : y ∉ XcL (P₁ ⊔ P₂) z t w := by
  rintro ((⟨hR, -⟩ | ⟨r, hr, hyr⟩) | ⟨r, hr, hyr⟩)
  · exact h.not_R_Rw hR hy
  · have hh : y * t ∈ P₁ ⊔ P₂ := by rw [hyr]; exact h.Az_coset hr
    exact h.not_Rt_Rw hh hy
  · have hh : y * (t * w) ∈ P₁ ⊔ P₂ := by rw [hyr]; exact h.Cz_coset hr
    exact h.not_Rw_Rtw hy hh

theorem part_conj_tw {g₁ g₂ : G} (h1 : g₁ ∈ P₁) (h2 : g₂ ∈ P₁) :
    rr t g₁ g₂ * (t * w) * (rr t g₁ g₂)⁻¹ =
      rr t (g₁ * (w * g₂ * w⁻¹)⁻¹) (g₂ * (w * g₁ * w⁻¹)⁻¹) * (t * w) := by
  have hd := h.toPsp4
  have hw1 : w * g₁ * w⁻¹ ∈ P₁ := h.w_norm g₁ h1
  have hw2 : w * g₂ * w⁻¹ ∈ P₁ := h.w_norm g₂ h2
  have e1 : (t * w) * (rr t g₁ g₂)⁻¹ * (t * w)⁻¹ = rr t (w * g₂ * w⁻¹)⁻¹ (w * g₁ * w⁻¹)⁻¹ := by
    have e2 : (t * w) * (rr t g₁ g₂)⁻¹ * (t * w)⁻¹ = (t * (w * rr t g₁ g₂ * w⁻¹) * t⁻¹)⁻¹ := by group
    rw [e2, h.w_rr, hd.σ_rr hw1 hw2, hd.rr_inv hw2 hw1]
  calc rr t g₁ g₂ * (t * w) * (rr t g₁ g₂)⁻¹
      = rr t g₁ g₂ * ((t * w) * (rr t g₁ g₂)⁻¹ * (t * w)⁻¹) * (t * w) := by group
    _ = rr t g₁ g₂ * rr t (w * g₂ * w⁻¹)⁻¹ (w * g₁ * w⁻¹)⁻¹ * (t * w) := by rw [e1]
    _ = rr t (g₁ * (w * g₂ * w⁻¹)⁻¹) (g₂ * (w * g₁ * w⁻¹)⁻¹) * (t * w) := by
      rw [hd.rr_mul h2 (inv_mem hw2)]

theorem rrtw_sq {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    (rr t p q * (t * w)) * (rr t p q * (t * w)) = rr t (p * (w * q * w⁻¹)) (q * (w * p * w⁻¹)) := by
  have hd := h.toPsp4
  have hwp : w * p * w⁻¹ ∈ P₁ := h.w_norm p hp
  have hwq : w * q * w⁻¹ ∈ P₁ := h.w_norm q hq
  have e : (t * w) * rr t p q = rr t (w * q * w⁻¹) (w * p * w⁻¹) * (t * w) := by
    calc (t * w) * rr t p q = (t * (w * rr t p q * w⁻¹) * t⁻¹) * (t * w) := by group
      _ = rr t (w * q * w⁻¹) (w * p * w⁻¹) * (t * w) := by rw [h.w_rr, hd.σ_rr hwp hwq]
  calc (rr t p q * (t * w)) * (rr t p q * (t * w))
      = rr t p q * ((t * w) * rr t p q) * (t * w) := by simp only [mul_assoc]
    _ = rr t p q * (rr t (w * q * w⁻¹) (w * p * w⁻¹) * (t * w)) * (t * w) := by rw [e]
    _ = (rr t p q * rr t (w * q * w⁻¹) (w * p * w⁻¹)) * ((t * w) * (t * w)) := by simp only [mul_assoc]
    _ = rr t (p * (w * q * w⁻¹)) (q * (w * p * w⁻¹)) := by rw [h.tw_sq, mul_one, hd.rr_mul hq hwq]

theorem rrtw_sq_iff {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    (rr t p q * (t * w)) * (rr t p q * (t * w)) = 1 ↔
      p * (w * q * w⁻¹) = 1 ∨ p * (w * q * w⁻¹) = z := by
  have hd := h.toPsp4
  have hwp : w * p * w⁻¹ ∈ P₁ := h.w_norm p hp
  have hwq : w * q * w⁻¹ ∈ P₁ := h.w_norm q hq
  have e : (rr t p q * (t * w)) * (rr t p q * (t * w)) = 1 ↔
      rr t (p * (w * q * w⁻¹)) (q * (w * p * w⁻¹)) = rr t 1 1 := by
    rw [h.rrtw_sq hp hq, Data.rr_one]
  rw [e, hd.rr_eq_iff (mul_mem hp hwq) (mul_mem hq hwp) (one_mem _) (one_mem _)]
  have hω : ∀ c : G, p * (w * q * w⁻¹) = c → (w * p * w⁻¹) * q = w * c * w⁻¹ := by
    intro c hc
    have h1 : w * (p * (w * q * w⁻¹)) * w⁻¹ = w * c * w⁻¹ := by rw [hc]
    rw [conj_mul' w, h.ω_ω] at h1
    exact h1
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact Or.inl h1.symm
    · refine Or.inr ?_
      calc p * (w * q * w⁻¹) = z⁻¹ * (z * (p * (w * q * w⁻¹))) := by group
        _ = z := by rw [← h1, mul_one, h.z_inv]
  · rintro (h1 | h1)
    · refine Or.inl ⟨h1.symm, ?_⟩
      have h2 := hω 1 h1
      rw [show w * (1 : G) * w⁻¹ = 1 by group] at h2
      exact (mul_eq_one_comm.1 h2).symm
    · refine Or.inr ⟨by rw [h1, h.z_sq], ?_⟩
      have h2 := hω z h1
      rw [h.ω_z] at h2
      have h3 : q * (w * p * w⁻¹) = z := hd.part_mul_eq_z_comm hwp h2
      rw [h3, h.z_sq]

omit [Finite G] in
theorem q_eq_of_one {p q : G} (h1 : p * (w * q * w⁻¹) = 1) : q = (w * p * w⁻¹)⁻¹ := by
  have h2 : w * q * w⁻¹ = p⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : q = w * p⁻¹ * w⁻¹ := by
    have h4 : w * (w * q * w⁻¹) * w⁻¹ = w * p⁻¹ * w⁻¹ := by rw [h2]
    rw [h.ω_ω] at h4
    exact h4
  rw [h3, conj_inv' w]

omit [Finite G] in
theorem q_eq_of_z {p q : G} (hp : p ∈ P₁) (h1 : p * (w * q * w⁻¹) = z) :
    q = z * (w * p * w⁻¹)⁻¹ := by
  have h2 : w * q * w⁻¹ = p⁻¹ * z := by
    calc w * q * w⁻¹ = p⁻¹ * (p * (w * q * w⁻¹)) := by group
      _ = p⁻¹ * z := by rw [h1]
  have h3 : q = w * (p⁻¹ * z) * w⁻¹ := by
    have h4 : w * (w * q * w⁻¹) * w⁻¹ = w * (p⁻¹ * z) * w⁻¹ := by rw [h2]
    rw [h.ω_ω] at h4
    exact h4
  have hwp : w * p * w⁻¹ ∈ P₁ := h.w_norm p hp
  have hc : z * (w * p * w⁻¹)⁻¹ = (w * p * w⁻¹)⁻¹ * z := h.z_comm (h.P₁_le (inv_mem hwp))
  rw [h3, conj_mul' w, conj_inv' w, h.ω_z, hc]

theorem rrtw_mem_ZcL_iff {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * (t * w) ∈ ZcL (P₁ ⊔ P₂) z t w ↔ q = (w * p * w⁻¹)⁻¹ := by
  have hd := h.toPsp4
  have hR : rr t p q ∈ P₁ ⊔ P₂ := hd.rr_mem_R hp hq
  have hRtw : rr t p q * (t * w) * (t * w) ∈ P₁ ⊔ P₂ := by rw [mul_assoc, h.tw_sq, mul_one]; exact hR
  have hwp : w * p * w⁻¹ ∈ P₁ := h.w_norm p hp
  constructor
  · rintro (((hz | ⟨r, hr, hyr⟩) | ⟨⟨r, hr, hyr⟩, -⟩) | ⟨r, hr, hyr⟩)
    · exfalso
      have hz' : rr t p q * (t * w) = z := hz
      have hzR : rr t p q * (t * w) ∈ P₁ ⊔ P₂ := by rw [hz']; exact h.z_mem_R
      exact h.not_R_Rtw hzR hRtw
    · exfalso
      have hh : (rr t p q * (t * w)) * t ∈ P₁ ⊔ P₂ := by rw [hyr]; exact h.A_coset hr
      exact h.not_Rt_Rtw hh hRtw
    · exfalso
      have hh : (rr t p q * (t * w)) * w ∈ P₁ ⊔ P₂ := by
        rw [hyr, mul_assoc, h.w_inv, mul_one]; exact hr
      exact h.not_Rw_Rtw hh hRtw
    · obtain ⟨g₁, h1, g₂, h2, rfl⟩ := hd.mem_R_iff.1 hr
      rw [h.part_conj_tw h1 h2] at hyr
      have hrr : rr t p q = rr t (g₁ * (w * g₂ * w⁻¹)⁻¹) (g₂ * (w * g₁ * w⁻¹)⁻¹) :=
        mul_right_cancel hyr
      have hq1 : g₂ * (w * g₁ * w⁻¹)⁻¹ ∈ P₁ := mul_mem h2 (h.ω_inv_mem h1)
      have hp1 : g₁ * (w * g₂ * w⁻¹)⁻¹ ∈ P₁ := mul_mem h1 (h.ω_inv_mem h2)
      rcases (hd.rr_eq_iff hp hq hp1 hq1).1 hrr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2, conj_mul' w, conj_inv' w, h.ω_ω]
        group
      · have e3 : p = z * (g₁ * (w * g₂ * w⁻¹)⁻¹) := by
          calc p = (z * z) * p := by rw [h.z_sq, one_mul]
            _ = z * (z * p) := by rw [mul_assoc]
            _ = z * (g₁ * (w * g₂ * w⁻¹)⁻¹) := by rw [← e1]
        have e4 : w * p * w⁻¹ = z * (w * g₁ * w⁻¹ * g₂⁻¹) := by
          rw [e3, conj_mul' w, h.ω_z, conj_mul' w, conj_inv' w, h.ω_ω]
        rw [e4]
        have hzc : z * q = q * z := h.z_comm (h.P₁_le hq)
        have e6 : (z * (w * g₁ * w⁻¹ * g₂⁻¹))⁻¹ = (g₂ * (w * g₁ * w⁻¹)⁻¹) * z := by
          rw [mul_inv_rev, mul_inv_rev, inv_inv, h.z_inv]
        rw [e6, e2]
        calc q = (z * z) * q := by rw [h.z_sq, one_mul]
          _ = z * (z * q) := by rw [mul_assoc]
          _ = z * (q * z) := by rw [hzc]
          _ = z * q * z := by rw [mul_assoc]
  · intro hq'
    refine Or.inr ⟨rr t p 1, hd.rr_mem_R hp (one_mem _), ?_⟩
    rw [h.part_conj_tw hp (one_mem _)]
    have e5 : w * (1 : G) * w⁻¹ = 1 := by group
    rw [e5, inv_one, mul_one, one_mul, hq']

omit [Finite G] in
theorem key_ω (g₁ g₂ : G) :
    (w * (g₁ * (w * g₂ * w⁻¹)⁻¹) * w⁻¹)⁻¹ = g₂ * (w * g₁ * w⁻¹)⁻¹ := by
  rw [conj_mul' w, conj_inv' w, h.ω_ω]; group

theorem rrtw_mem_XcL_iff {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * (t * w) ∈ XcL (P₁ ⊔ P₂) z t w ↔ q = z * (w * p * w⁻¹)⁻¹ := by
  have hd := h.toPsp4
  have hR : rr t p q ∈ P₁ ⊔ P₂ := hd.rr_mem_R hp hq
  have hRtw : rr t p q * (t * w) * (t * w) ∈ P₁ ⊔ P₂ := by rw [mul_assoc, h.tw_sq, mul_one]; exact hR
  have hwp : w * p * w⁻¹ ∈ P₁ := h.w_norm p hp
  have hzq : z * q = q * z := h.z_comm (h.P₁_le hq)
  constructor
  · rintro ((⟨hRR, -⟩ | ⟨r, hr, hyr⟩) | ⟨r, hr, hyr⟩)
    · exfalso
      exact h.not_R_Rtw hRR hRtw
    · exfalso
      have hh : (rr t p q * (t * w)) * t ∈ P₁ ⊔ P₂ := by rw [hyr]; exact h.Az_coset hr
      exact h.not_Rt_Rtw hh hRtw
    · obtain ⟨g₁, h1, g₂, h2, rfl⟩ := hd.mem_R_iff.1 hr
      have hsv : rr t g₁ g₂ * (t * w * z) * (rr t g₁ g₂)⁻¹ =
          z * (rr t g₁ g₂ * (t * w) * (rr t g₁ g₂)⁻¹) :=
        h.conj_mul_z (h.R_mem_S (hd.rr_mem_R h1 h2)) (mul_mem h.t_mem h.w_mem)
      rw [hsv, h.part_conj_tw h1 h2, ← mul_assoc z _ (t * w), z_mul_rr_left] at hyr
      have hrr : rr t p q = rr t (z * (g₁ * (w * g₂ * w⁻¹)⁻¹)) (g₂ * (w * g₁ * w⁻¹)⁻¹) :=
        mul_right_cancel hyr
      have hq1 : g₂ * (w * g₁ * w⁻¹)⁻¹ ∈ P₁ := mul_mem h2 (h.ω_inv_mem h1)
      have hp1 : z * (g₁ * (w * g₂ * w⁻¹)⁻¹) ∈ P₁ := mul_mem h.z_mem₁ (mul_mem h1 (h.ω_inv_mem h2))
      rcases (hd.rr_eq_iff hp hq hp1 hq1).1 hrr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      ·
        have hinv : (w * p * w⁻¹)⁻¹ = q * z := by
          rw [← e1, conj_mul' w, h.ω_z, mul_inv_rev, h.key_ω, h.z_inv, e2]
        rw [hinv]
        calc q = (z * z) * q := by rw [h.z_sq, one_mul]
          _ = z * (z * q) := by rw [mul_assoc]
          _ = z * (q * z) := by rw [hzq]
      ·
        have e3 : g₁ * (w * g₂ * w⁻¹)⁻¹ = p := mul_left_cancel e1
        have hinv : (w * p * w⁻¹)⁻¹ = z * q := by
          rw [← e3, h.key_ω, e2]
        rw [hinv]
        calc q = (z * z) * q := by rw [h.z_sq, one_mul]
          _ = z * (z * q) := by rw [mul_assoc]
  · intro hq'
    refine Or.inr ⟨rr t (z * p) 1, hd.rr_mem_R (mul_mem h.z_mem₁ hp) (one_mem _), ?_⟩
    have hsv : rr t (z * p) 1 * (t * w * z) * (rr t (z * p) 1)⁻¹ =
        z * (rr t (z * p) 1 * (t * w) * (rr t (z * p) 1)⁻¹) :=
      h.conj_mul_z (h.R_mem_S (hd.rr_mem_R (mul_mem h.z_mem₁ hp) (one_mem _)))
        (mul_mem h.t_mem h.w_mem)
    rw [hsv, h.part_conj_tw (mul_mem h.z_mem₁ hp) (one_mem _), ← mul_assoc z _ (t * w), z_mul_rr_left]
    have e5 : w * (1 : G) * w⁻¹ = 1 := by group
    have c1 : z * (z * p * (w * (1 : G) * w⁻¹)⁻¹) = p := by
      rw [e5, inv_one, mul_one, ← mul_assoc, h.z_sq, one_mul]
    have c2 : (1 : G) * (w * (z * p) * w⁻¹)⁻¹ = q := by
      have hc : (w * p * w⁻¹)⁻¹ * z = z * (w * p * w⁻¹)⁻¹ := (h.z_comm (h.P₁_le (h.ω_inv_mem hp))).symm
      rw [one_mul, conj_mul' w, h.ω_z, mul_inv_rev, h.z_inv, hc, hq']
    rw [c1, c2]

theorem partition : ∀ y ∈ S, y * y = 1 → y ≠ 1 →
    (y ∈ ZcL (P₁ ⊔ P₂) z t w ∨ y ∈ XcL (P₁ ⊔ P₂) z t w) ∧
      ¬ (y ∈ ZcL (P₁ ⊔ P₂) z t w ∧ y ∈ XcL (P₁ ⊔ P₂) z t w) := by
  intro y hy hy2 hy1
  have hd := h.toPsp4
  obtain ⟨p, hp, q, hq, hyy | hyy | hyy | hyy⟩ := h.mem_S_iff.1 hy
  · have hyR : y ∈ P₁ ⊔ P₂ := hyy ▸ hd.rr_mem_R hp hq
    by_cases hyz : y = z
    · refine ⟨Or.inl ((h.mem_ZcL_R hyR).2 hyz), ?_⟩
      rintro ⟨-, hX⟩
      exact ((h.mem_XcL_R hyR).1 hX).2.2 hyz
    · refine ⟨Or.inr ((h.mem_XcL_R hyR).2 ⟨hy2, hy1, hyz⟩), ?_⟩
      rintro ⟨hZ, -⟩
      exact hyz ((h.mem_ZcL_R hyR).1 hZ)
  · subst hyy
    rcases (hd.rrt_sq_iff hp hq).1 hy2 with h1 | h1
    · refine ⟨Or.inl ((h.rrt_mem_ZcL_iff hp hq).2 h1), ?_⟩
      rintro ⟨-, hX⟩
      exact h.z_ne_one (((h.rrt_mem_XcL_iff hp hq).1 hX).symm.trans h1)
    · refine ⟨Or.inr ((h.rrt_mem_XcL_iff hp hq).2 h1), ?_⟩
      rintro ⟨hZ, -⟩
      exact h.z_ne_one (h1.symm.trans ((h.rrt_mem_ZcL_iff hp hq).1 hZ))
  · have hyw : y * w ∈ P₁ ⊔ P₂ := by
      rw [hyy, mul_assoc, h.w_inv, mul_one]; exact hd.rr_mem_R hp hq
    exact ⟨Or.inl (h.mem_ZcL_Rw hyw hy2), fun hboth => h.not_mem_XcL_Rw hyw hboth.2⟩
  · subst hyy
    rcases (h.rrtw_sq_iff hp hq).1 hy2 with h1 | h1
    · refine ⟨Or.inl ((h.rrtw_mem_ZcL_iff hp hq).2 (h.q_eq_of_one h1)), ?_⟩
      rintro ⟨-, hX⟩
      have h3 := (h.rrtw_mem_XcL_iff hp hq).1 hX
      rw [h.q_eq_of_one h1] at h3
      have : (1 : G) = z := by
        calc (1 : G) = ((w * p * w⁻¹)⁻¹)⁻¹ * ((w * p * w⁻¹)⁻¹) := by group
          _ = ((w * p * w⁻¹)⁻¹)⁻¹ * (z * (w * p * w⁻¹)⁻¹) := by rw [← h3]
          _ = z := by
            have hc : z * (w * p * w⁻¹)⁻¹ = (w * p * w⁻¹)⁻¹ * z :=
              h.z_comm (h.P₁_le (h.ω_inv_mem hp))
            rw [hc]; group
      exact h.z_ne_one this.symm
    · refine ⟨Or.inr ((h.rrtw_mem_XcL_iff hp hq).2 (h.q_eq_of_z hp h1)), ?_⟩
      rintro ⟨hZ, -⟩
      have h3 := (h.rrtw_mem_ZcL_iff hp hq).1 hZ
      rw [h.q_eq_of_z hp h1] at h3
      have hc : z * (w * p * w⁻¹)⁻¹ = (w * p * w⁻¹)⁻¹ * z :=
        h.z_comm (h.P₁_le (h.ω_inv_mem hp))
      have : z = 1 := by
        calc z = ((w * p * w⁻¹)⁻¹)⁻¹ * (z * (w * p * w⁻¹)⁻¹) := by rw [hc]; group
          _ = ((w * p * w⁻¹)⁻¹)⁻¹ * ((w * p * w⁻¹)⁻¹) := by rw [h3]
          _ = 1 := by group
      exact h.z_ne_one this

theorem S_decomp {s : G} (hs : s ∈ S) :
    ∃ ρ ∈ P₁ ⊔ P₂, ∃ τ : G, (τ = 1 ∨ τ = t ∨ τ = w ∨ τ = t * w) ∧ s = ρ * τ := by
  have hd := h.toPsp4
  obtain ⟨p, hp, q, hq, rfl | rfl | rfl | rfl⟩ := h.mem_S_iff.1 hs
  · exact ⟨_, hd.rr_mem_R hp hq, 1, Or.inl rfl, (mul_one _).symm⟩
  · exact ⟨_, hd.rr_mem_R hp hq, t, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨_, hd.rr_mem_R hp hq, w, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨_, hd.rr_mem_R hp hq, t * w, Or.inr (Or.inr (Or.inr rfl)), rfl⟩

theorem V_conj_R {τ r : G} (hτ : τ = 1 ∨ τ = t ∨ τ = w ∨ τ = t * w) (hr : r ∈ P₁ ⊔ P₂) :
    τ * r * τ⁻¹ ∈ P₁ ⊔ P₂ := by
  rcases hτ with rfl | rfl | rfl | rfl
  · simpa using hr
  · exact h.t_conj_R hr
  · exact h.w_conj_R hr
  · have e : t * w * r * (t * w)⁻¹ = t * (w * r * w⁻¹) * t⁻¹ := by group
    rw [e]
    exact h.t_conj_R (h.w_conj_R hr)

omit [Finite G] in
theorem V_comm {τ c : G} (ht : t * c = c * t) (hw : w * c = c * w)
    (hτ : τ = 1 ∨ τ = t ∨ τ = w ∨ τ = t * w) : τ * c = c * τ := by
  rcases hτ with rfl | rfl | rfl | rfl
  · simp
  · exact ht
  · exact hw
  · calc t * w * c = t * (w * c) := by rw [mul_assoc]
      _ = t * (c * w) := by rw [hw]
      _ = (t * c) * w := by rw [mul_assoc]
      _ = (c * t) * w := by rw [ht]
      _ = c * (t * w) := by rw [mul_assoc]

theorem conj_class {c r s : G} (ht : t * c = c * t) (hw : w * c = c * w) (hs : s ∈ S)
    (hr : r ∈ P₁ ⊔ P₂) : ∃ r' ∈ P₁ ⊔ P₂, s * (r * c * r⁻¹) * s⁻¹ = r' * c * r'⁻¹ := by
  obtain ⟨ρ, hρ, τ, hτ, rfl⟩ := h.S_decomp hs
  have hτc : τ * c * τ⁻¹ = c := by
    rw [h.V_comm ht hw hτ]; group
  refine ⟨ρ * (τ * r * τ⁻¹), mul_mem hρ (h.V_conj_R hτ hr), ?_⟩
  calc ρ * τ * (r * c * r⁻¹) * (ρ * τ)⁻¹
      = ρ * ((τ * r * τ⁻¹) * (τ * c * τ⁻¹) * (τ * r * τ⁻¹)⁻¹) * ρ⁻¹ := by group
    _ = ρ * (τ * r * τ⁻¹) * c * (ρ * (τ * r * τ⁻¹))⁻¹ := by rw [hτc]; group

omit [Finite G] in
theorem t_comm_tw : t * (t * w) = (t * w) * t := by rw [mul_assoc t w t, h.wt_comm]

omit [Finite G] in
theorem w_comm_tw : w * (t * w) = (t * w) * w := by rw [← mul_assoc, h.wt_comm]

omit [Finite G] in
theorem comm_mul_z {c : G} (ht : t * c = c * t) (hw : w * c = c * w) :
    t * (c * z) = (c * z) * t ∧ w * (c * z) = (c * z) * w := by
  constructor
  · calc t * (c * z) = (t * c) * z := by rw [mul_assoc]
      _ = (c * t) * z := by rw [ht]
      _ = c * (t * z) := by rw [mul_assoc]
      _ = c * (z * t) := by rw [h.z_cent t h.t_mem]
      _ = (c * z) * t := by rw [mul_assoc]
  · calc w * (c * z) = (w * c) * z := by rw [mul_assoc]
      _ = (c * w) * z := by rw [hw]
      _ = c * (w * z) := by rw [mul_assoc]
      _ = c * (z * w) := by rw [h.z_cent w h.w_mem]
      _ = (c * z) * w := by rw [mul_assoc]

theorem ZcL_conj {s x : G} (hs : s ∈ S) (hx : x ∈ ZcL (P₁ ⊔ P₂) z t w) :
    s * x * s⁻¹ ∈ ZcL (P₁ ⊔ P₂) z t w := by
  rcases hx with (((hz | ⟨r, hr, rfl⟩) | ⟨⟨r, hr, rfl⟩, hsq⟩) | ⟨r, hr, rfl⟩)
  · have hz' : x = z := hz
    rw [hz', h.z_cent s hs, mul_assoc, mul_inv_cancel, mul_one]
    exact Or.inl (Or.inl (Or.inl rfl))
  · obtain ⟨r', hr', hrr'⟩ := h.conj_class (c := t) rfl h.wt_comm hs hr
    exact Or.inl (Or.inl (Or.inr ⟨r', hr', hrr'⟩))
  · obtain ⟨ρ, hρ, τ, hτ, rfl⟩ := h.S_decomp hs
    have hτw : τ * w * τ⁻¹ = w := by
      rw [h.V_comm h.tw_comm rfl hτ]; group
    have hr'' : ρ * (τ * r * τ⁻¹) * (w * ρ⁻¹ * w⁻¹) ∈ P₁ ⊔ P₂ :=
      mul_mem (mul_mem hρ (h.V_conj_R hτ hr)) (h.w_conj_R (inv_mem hρ))
    have e : ρ * τ * (r * w) * (ρ * τ)⁻¹ = (ρ * (τ * r * τ⁻¹) * (w * ρ⁻¹ * w⁻¹)) * w := by
      calc ρ * τ * (r * w) * (ρ * τ)⁻¹
          = ρ * ((τ * r * τ⁻¹) * (τ * w * τ⁻¹)) * ρ⁻¹ := by group
        _ = ρ * ((τ * r * τ⁻¹) * w) * ρ⁻¹ := by rw [hτw]
        _ = (ρ * (τ * r * τ⁻¹) * (w * ρ⁻¹ * w⁻¹)) * w := by group
    refine Or.inl (Or.inr ⟨⟨_, hr'', e⟩, ?_⟩)
    have e2 : ρ * τ * (r * w) * (ρ * τ)⁻¹ * (ρ * τ * (r * w) * (ρ * τ)⁻¹) =
        (ρ * τ) * ((r * w) * (r * w)) * (ρ * τ)⁻¹ := by group
    rw [e2, hsq, mul_one, mul_inv_cancel]
  · obtain ⟨r', hr', hrr'⟩ := h.conj_class (c := t * w) h.t_comm_tw h.w_comm_tw hs hr
    exact Or.inr ⟨r', hr', hrr'⟩

theorem XcL_conj {s x : G} (hs : s ∈ S) (hx : x ∈ XcL (P₁ ⊔ P₂) z t w) :
    s * x * s⁻¹ ∈ XcL (P₁ ⊔ P₂) z t w := by
  rcases hx with ((⟨hxR, hsq, hx1, hxz⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩)
  · refine Or.inl (Or.inl ⟨h.S_conj_R hs hxR, ?_, ?_, ?_⟩)
    · have e2 : s * x * s⁻¹ * (s * x * s⁻¹) = s * (x * x) * s⁻¹ := by group
      rw [e2, hsq, mul_one, mul_inv_cancel]
    · intro h1
      apply hx1
      have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      rw [this, h1]; group
    · intro h1
      apply hxz
      have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      rw [this, h1]
      calc s⁻¹ * z * s = s⁻¹ * (z * s) := by rw [mul_assoc]
        _ = s⁻¹ * (s * z) := by rw [h.z_cent s hs]
        _ = z := by group
  · have hc := h.comm_mul_z (c := t) rfl h.wt_comm
    obtain ⟨r', hr', hrr'⟩ := h.conj_class (c := t * z) hc.1 hc.2 hs hr
    exact Or.inl (Or.inr ⟨r', hr', hrr'⟩)
  · have hc := h.comm_mul_z (c := t * w) h.t_comm_tw h.w_comm_tw
    obtain ⟨r', hr', hrr'⟩ := h.conj_class (c := t * w * z) hc.1 hc.2 hs hr
    exact Or.inr ⟨r', hr', hrr'⟩

end DataL4

end CFSG.GH74.GLS.Stage2.Local.P27.L4
