module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56C2a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y56_z_comm_S {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {x : G} (hx : x ∈ s.fr.S) : s.fr.z * x = x * s.fr.z := by
  have hcen : cen s.fr.S = s.fr.Z := hH.hLF.fact14.1.1
  have hz : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) := by
    have hmem : s.fr.z ∈ cen s.fr.S := hcen.symm ▸ Subgroup.mem_zpowers s.fr.z
    exact (Subgroup.mem_inf.mp hmem).2
  exact (Subgroup.mem_centralizer_iff.mp hz x hx).symm

private theorem y56_conj_eq_scalar_mul {x y w : G} (h : ⁅x, y⁆ = w) :
    x * y * x⁻¹ = w * y := by
  rw [commutatorElement_def] at h
  calc x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    _ = w * y := by rw [h]

private theorem y56_conj_eq_inv_mul {x y w : G} (h : ⁅x, y⁆ = w) :
    y * x * y⁻¹ = w⁻¹ * x := by
  rw [commutatorElement_def] at h
  have h1 : y * x⁻¹ * y⁻¹ = x⁻¹ * w := by
    have h2 : x * (y * x⁻¹ * y⁻¹) = x * (x⁻¹ * w) := by
      calc x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by group
        _ = w := h
        _ = x * (x⁻¹ * w) := by group
    exact mul_left_cancel h2
  calc y * x * y⁻¹ = (y * x⁻¹ * y⁻¹)⁻¹ := by group
    _ = (x⁻¹ * w)⁻¹ := by rw [h1]
    _ = w⁻¹ * x := by group

private theorem y56_conj_inv_scalar {x y w : G} (h : ⁅x, y⁆ = w) (hw : w ^ 2 = 1) :
    y * x * y⁻¹ = w * x := by
  have hwinv : w⁻¹ = w := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]
    exact hw
  have h' : ⁅y, x⁆ = w := by rw [← commutatorElement_inv, h, hwinv]
  exact y56_conj_eq_scalar_mul h'

private theorem y56_mem_B_of_conj {s : Setting3 G L} {x : G} (hxS : x ∈ s.fr.S)
    (hx : x * (s.fr.b₁ * s.fr.b₂) * x⁻¹ = s.fr.b₁ * s.fr.b₂) : x ∈ s.fr.B := by
  rw [SFrame.B, centIn, Subgroup.centralizer_closure, Subgroup.mem_inf]
  refine ⟨hxS, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have h : x * (s.fr.b₁ * s.fr.b₂) = (s.fr.b₁ * s.fr.b₂) * x := by
    calc x * (s.fr.b₁ * s.fr.b₂) = (x * (s.fr.b₁ * s.fr.b₂) * x⁻¹) * x := by group
      _ = (s.fr.b₁ * s.fr.b₂) * x := by rw [hx]
  exact h.symm

private theorem y56_b1_conj_v0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹ = s.fr.b₁ * s.fr.b₂ := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have hc : Commute s.fr.b₁ s.fr.b₂ :=
    commutatorElement_eq_one_iff_commute.mp hsrel.b1b2
  calc s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹
      = s.fr.b₁ * s.fr.b₁ * (s.fr.b₂ * s.fr.b₁⁻¹) := by group
    _ = s.fr.b₁ * s.fr.b₁ * (s.fr.b₁⁻¹ * s.fr.b₂) := by rw [hc.symm.inv_right.eq]
    _ = s.fr.b₁ * s.fr.b₂ := by group

private theorem y56_h0_conj_v0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.h₀ * (s.fr.b₁ * s.fr.b₂) * s.fr.h₀⁻¹ = s.fr.b₁ * s.fr.b₂ := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have hzsq : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hsrel.z_sq
  calc s.fr.h₀ * (s.fr.b₁ * s.fr.b₂) * s.fr.h₀⁻¹
      = (s.fr.h₀ * s.fr.b₁ * s.fr.h₀⁻¹) * (s.fr.h₀ * s.fr.b₂ * s.fr.h₀⁻¹) := by group
    _ = (s.fr.z * s.fr.b₁) * (s.fr.z * s.fr.b₂) := by
          rw [y56_conj_inv_scalar hsrel.b1h hsrel.z_sq,
            y56_conj_inv_scalar hsrel.b2h hsrel.z_sq]
    _ = s.fr.b₁ * s.fr.b₂ := by
          rw [y56_z_comm_S hH (s3_b₁_mem_S s)]
          rw [show (s.fr.b₁ * s.fr.z) * (s.fr.z * s.fr.b₂)
              = s.fr.b₁ * (s.fr.z * s.fr.z) * s.fr.b₂ from by group]
          rw [hzsq]; group

private theorem y56_b1_conj_e0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.b₁ * y56e0 s * s.fr.b₁⁻¹ = s.fr.z * y56e0 s := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have hb1a1 : s.fr.b₁ * s.fr.a₁ * s.fr.b₁⁻¹ = s.fr.z * s.fr.a₁ :=
    y56_conj_inv_scalar hsrel.comm1 hsrel.z_sq
  have hb1a2 : s.fr.b₁ * s.fr.a₂ * s.fr.b₁⁻¹ = s.fr.a₂ := by
    rw [commutatorElement_eq_one_iff_mul_comm.mp hsrel.b1a2]; group
  change s.fr.b₁ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.b₁⁻¹
      = s.fr.z * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂)
  calc s.fr.b₁ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.b₁⁻¹
      = (s.fr.b₁ * s.fr.a₁ * s.fr.b₁⁻¹) * s.fr.b₁ *
          (s.fr.b₁ * s.fr.a₂ * s.fr.b₁⁻¹) := by group
    _ = (s.fr.z * s.fr.a₁) * s.fr.b₁ * s.fr.a₂ := by rw [hb1a1, hb1a2]
    _ = s.fr.z * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) := by group

private theorem y56_h0_conj_e0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.h₀ * y56e0 s * s.fr.h₀⁻¹
      = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * y56e0 s := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have hzsq : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hsrel.z_sq
  have hb1sq : s.fr.b₁ * s.fr.b₁ = s.fr.z := by rw [← pow_two, SFrame.z]
  have hzb1 : s.fr.z * s.fr.b₁ = s.fr.b₁ * s.fr.z := y56_z_comm_S hH (s3_b₁_mem_S s)
  have hza1 : s.fr.z * s.fr.a₁ = s.fr.a₁ * s.fr.z := y56_z_comm_S hH (s3_a₁_mem_S s)
  have ha1b2 : s.fr.a₁ * s.fr.b₂ = s.fr.b₂ * s.fr.a₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp hsrel.a1b2
  have hb1b2 : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp hsrel.b1b2
  have hb1a1 : s.fr.b₁ * s.fr.a₁ = s.fr.z * s.fr.a₁ * s.fr.b₁ := by
    calc s.fr.b₁ * s.fr.a₁ = (s.fr.b₁ * s.fr.a₁ * s.fr.b₁⁻¹) * s.fr.b₁ := by group
      _ = (s.fr.z * s.fr.a₁) * s.fr.b₁ := by
            rw [y56_conj_inv_scalar hsrel.comm1 hsrel.z_sq]
  have hb1a1b1 : s.fr.b₁ * s.fr.a₁ * s.fr.b₁ = s.fr.a₁ := by
    calc s.fr.b₁ * s.fr.a₁ * s.fr.b₁
        = (s.fr.b₁ * s.fr.a₁ * s.fr.b₁⁻¹) * (s.fr.b₁ * s.fr.b₁) := by group
      _ = (s.fr.z * s.fr.a₁) * (s.fr.b₁ * s.fr.b₁) := by
            rw [y56_conj_inv_scalar hsrel.comm1 hsrel.z_sq]
      _ = (s.fr.z * s.fr.a₁) * s.fr.z := by rw [hb1sq]
      _ = s.fr.a₁ := by
            rw [hza1]
            rw [show s.fr.a₁ * s.fr.z * s.fr.z = s.fr.a₁ * (s.fr.z * s.fr.z) from by group]
            rw [hzsq]; group
  have hh0a1 : s.fr.h₀ * s.fr.a₁ * s.fr.h₀⁻¹ = s.fr.b₁ * s.fr.a₁ := by
    have h := y56_conj_eq_inv_mul hsrel.a1h
    have hb1z : (s.fr.b₁ * s.fr.z)⁻¹ = s.fr.b₁ := by
      rw [inv_eq_iff_mul_eq_one]
      calc s.fr.b₁ * s.fr.z * s.fr.b₁ = s.fr.b₁ * (s.fr.z * s.fr.b₁) := by group
        _ = s.fr.b₁ * (s.fr.b₁ * s.fr.z) := by rw [hzb1]
        _ = s.fr.b₁ * s.fr.b₁ * s.fr.z := by group
        _ = s.fr.z * s.fr.z := by rw [hb1sq]
        _ = 1 := hzsq
    rw [h, hb1z]
  have hh0b1 : s.fr.h₀ * s.fr.b₁ * s.fr.h₀⁻¹ = s.fr.z * s.fr.b₁ :=
    y56_conj_inv_scalar hsrel.b1h hsrel.z_sq
  have hh0a2 : s.fr.h₀ * s.fr.a₂ * s.fr.h₀⁻¹ = s.fr.b₂ * s.fr.a₂ := by
    have h := y56_conj_eq_inv_mul hsrel.a2h
    have hb2z : (s.fr.b₂ * s.fr.z)⁻¹ = s.fr.b₂ := by
      rw [inv_eq_iff_mul_eq_one]
      calc s.fr.b₂ * s.fr.z * s.fr.b₂ = s.fr.b₂ * (s.fr.z * s.fr.b₂) := by group
        _ = s.fr.b₂ * (s.fr.b₂ * s.fr.z) := by rw [y56_z_comm_S hH (s3_b₂_mem_S s)]
        _ = s.fr.b₂ * s.fr.b₂ * s.fr.z := by group
        _ = s.fr.z * s.fr.z := by rw [show s.fr.b₂ * s.fr.b₂ = s.fr.z from
              by rw [← pow_two]; exact hsrel.b2_sq]
        _ = 1 := hzsq
    rw [h, hb2z]
  have hh0b2 : s.fr.h₀ * s.fr.b₂ * s.fr.h₀⁻¹ = s.fr.z * s.fr.b₂ :=
    y56_conj_inv_scalar hsrel.b2h hsrel.z_sq
  have hL : (s.fr.b₁ * s.fr.a₁) * (s.fr.z * s.fr.b₁) * (s.fr.b₂ * s.fr.a₂)
      = s.fr.z * (s.fr.b₂ * (s.fr.a₁ * s.fr.a₂)) := by
    calc (s.fr.b₁ * s.fr.a₁) * (s.fr.z * s.fr.b₁) * (s.fr.b₂ * s.fr.a₂)
        = s.fr.z * (s.fr.a₁ * (s.fr.b₁ * (s.fr.z * s.fr.b₁) *
            (s.fr.b₂ * s.fr.a₂))) := by rw [hb1a1]; group
      _ = s.fr.z * (s.fr.a₁ * ((s.fr.b₁ * s.fr.z) * s.fr.b₁ *
            (s.fr.b₂ * s.fr.a₂))) := by group
      _ = s.fr.z * (s.fr.a₁ * ((s.fr.z * s.fr.b₁) * s.fr.b₁ *
            (s.fr.b₂ * s.fr.a₂))) := by rw [hzb1]
      _ = s.fr.z * (s.fr.a₁ * (s.fr.z * (s.fr.b₁ * s.fr.b₁) *
            (s.fr.b₂ * s.fr.a₂))) := by group
      _ = s.fr.z * (s.fr.a₁ * (s.fr.z * s.fr.z * (s.fr.b₂ * s.fr.a₂))) := by rw [hb1sq]
      _ = s.fr.z * (s.fr.a₁ * (s.fr.b₂ * s.fr.a₂)) := by rw [hzsq]; group
      _ = s.fr.z * (s.fr.b₂ * (s.fr.a₁ * s.fr.a₂)) := by
            rw [← mul_assoc s.fr.a₁ s.fr.b₂ s.fr.a₂, ha1b2]; group
  have hR : (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂)
      = s.fr.z * (s.fr.b₂ * (s.fr.a₁ * s.fr.a₂)) := by
    calc (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂)
        = s.fr.z * (s.fr.b₂ * (s.fr.b₁ * s.fr.a₁ * s.fr.b₁) * s.fr.a₂) := by
          rw [hb1b2]; group
      _ = s.fr.z * (s.fr.b₂ * s.fr.a₁ * s.fr.a₂) := by rw [hb1a1b1]
      _ = s.fr.z * (s.fr.b₂ * (s.fr.a₁ * s.fr.a₂)) := by group
  change s.fr.h₀ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.h₀⁻¹
      = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂)
  calc s.fr.h₀ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.h₀⁻¹
      = (s.fr.h₀ * s.fr.a₁ * s.fr.h₀⁻¹) * (s.fr.h₀ * s.fr.b₁ * s.fr.h₀⁻¹) *
          (s.fr.h₀ * s.fr.a₂ * s.fr.h₀⁻¹) := by group
    _ = (s.fr.b₁ * s.fr.a₁) * (s.fr.z * s.fr.b₁) * (s.fr.b₂ * s.fr.a₂) := by
          rw [hh0a1, hh0b1, hh0a2]
    _ = s.fr.z * (s.fr.b₂ * (s.fr.a₁ * s.fr.a₂)) := hL
    _ = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) := hR.symm

private theorem y56_b1h0_conj_e0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (s.fr.b₁ * s.fr.h₀) * y56e0 s * (s.fr.b₁ * s.fr.h₀)⁻¹
      = (s.fr.b₁ * s.fr.b₂) * y56e0 s := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have hzsq : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact hsrel.z_sq
  have hv0S : s.fr.b₁ * s.fr.b₂ ∈ s.fr.S := mul_mem (s3_b₁_mem_S s) (s3_b₂_mem_S s)
  have hb1z : s.fr.b₁ * s.fr.z * s.fr.b₁⁻¹ = s.fr.z := by
    have h := y56_z_comm_S hH (s3_b₁_mem_S s)
    rw [← h]; group
  have hb1v0 : s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹ = s.fr.b₁ * s.fr.b₂ :=
    y56_b1_conj_v0 hH
  have hb1zv0 : s.fr.b₁ * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.b₁⁻¹
      = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
    calc s.fr.b₁ * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.b₁⁻¹
        = (s.fr.b₁ * s.fr.z * s.fr.b₁⁻¹) *
            (s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹) := by group
      _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by rw [hb1z, hb1v0]
  have hb1e0 : s.fr.b₁ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.b₁⁻¹
      = s.fr.z * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) := y56_b1_conj_e0 hH
  have hh0e0 : s.fr.h₀ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.h₀⁻¹
      = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) :=
    y56_h0_conj_e0 hH
  change (s.fr.b₁ * s.fr.h₀) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) *
      (s.fr.b₁ * s.fr.h₀)⁻¹
    = (s.fr.b₁ * s.fr.b₂) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂)
  calc (s.fr.b₁ * s.fr.h₀) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) *
        (s.fr.b₁ * s.fr.h₀)⁻¹
      = s.fr.b₁ * (s.fr.h₀ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.h₀⁻¹) *
          s.fr.b₁⁻¹ := by group
    _ = s.fr.b₁ * ((s.fr.z * (s.fr.b₁ * s.fr.b₂)) *
          (s.fr.a₁ * s.fr.b₁ * s.fr.a₂)) * s.fr.b₁⁻¹ := by rw [hh0e0]
    _ = (s.fr.b₁ * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.b₁⁻¹) *
          (s.fr.b₁ * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) * s.fr.b₁⁻¹) := by group
    _ = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) *
          (s.fr.z * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂)) := by rw [hb1zv0, hb1e0]
    _ = (s.fr.b₁ * s.fr.b₂) * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) := by
          rw [y56_z_comm_S hH hv0S]
          rw [show (s.fr.b₁ * s.fr.b₂) * s.fr.z *
                (s.fr.z * (s.fr.a₁ * s.fr.b₁ * s.fr.a₂))
              = (s.fr.b₁ * s.fr.b₂) * (s.fr.z * s.fr.z) *
                  (s.fr.a₁ * s.fr.b₁ * s.fr.a₂) from by group]
          rw [hzsq]
          group

theorem y56_e0_mem_E (s : Setting3 G L) : y56e0 s ∈ s.fr.E := by
  rw [SFrame.E, y56e0]
  exact Subgroup.subset_closure (by simp)

theorem y56_E_eq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ f ∈ s.fr.E, ∃ κ ∈ cen s.fr.B, f = κ ∨ f = κ * y56e0 s := by
  intro f hf
  have hsrel := s3_srel hH.hS hH.hZ s
  have he0E : y56e0 s ∈ s.fr.E := y56_e0_mem_E s
  have he0B : y56e0 s ∈ s.fr.B := y56_E_le_B hH he0E
  have he0sq : y56e0 s * y56e0 s = 1 := by
    rw [← pow_two]; exact y56_E_sq hH (y56e0 s) he0E
  have he0inv : (y56e0 s)⁻¹ = y56e0 s := inv_eq_of_mul_eq_one_right he0sq
  have he0k : ∀ κ ∈ cen s.fr.B, y56e0 s * κ = κ * y56e0 s := by
    intro κ hκ
    have hκc : κ ∈ Subgroup.centralizer (s.fr.B : Set G) := (Subgroup.mem_inf.mp hκ).2
    exact Subgroup.mem_centralizer_iff.mp hκc (y56e0 s) he0B
  obtain ⟨hv0B, hzB, -, -, -, -⟩ := y56_v0 hH
  rw [SFrame.E] at hf
  refine Subgroup.closure_induction (p := fun f _ =>
    ∃ κ ∈ cen s.fr.B, f = κ ∨ f = κ * y56e0 s) ?_ ?_ ?_ ?_ hf
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨s.fr.b₁ * s.fr.b₂, hv0B, Or.inl rfl⟩
    · exact ⟨1, one_mem _, Or.inr (by rw [one_mul])⟩
    · exact ⟨s.fr.z, hzB, Or.inl rfl⟩
  · exact ⟨1, one_mem _, Or.inl rfl⟩
  · intro x y hx hy hpx hpy
    obtain ⟨κ, hκ, hx'⟩ := hpx
    obtain ⟨κ', hκ', hy'⟩ := hpy
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
    · exact ⟨κ * κ', mul_mem hκ hκ', Or.inl (by rw [hx', hy'])⟩
    · exact ⟨κ * κ', mul_mem hκ hκ', Or.inr (by rw [hx', hy']; group)⟩
    · refine ⟨κ * κ', mul_mem hκ hκ', Or.inr ?_⟩
      rw [hx', hy']
      rw [show (κ * y56e0 s) * κ' = κ * (y56e0 s * κ') from by group]
      rw [he0k κ' hκ']
      group
    · refine ⟨κ * κ', mul_mem hκ hκ', Or.inl ?_⟩
      rw [hx', hy']
      rw [show (κ * y56e0 s) * (κ' * y56e0 s) = κ * (y56e0 s * κ') * y56e0 s
            from by group]
      rw [he0k κ' hκ']
      rw [show κ * (κ' * y56e0 s) * y56e0 s = (κ * κ') * (y56e0 s * y56e0 s)
            from by group]
      rw [he0sq]
      group
  · intro x hx hpx
    obtain ⟨κ, hκ, hx'⟩ := hpx
    rcases hx' with hx' | hx'
    · exact ⟨κ⁻¹, inv_mem hκ, Or.inl (by rw [hx'])⟩
    · refine ⟨κ⁻¹, inv_mem hκ, Or.inr ?_⟩
      rw [hx', mul_inv_rev, he0inv]
      exact he0k κ⁻¹ (inv_mem hκ)

theorem y56_B_conj_e0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ κ ∈ cen s.fr.B, ∃ b ∈ s.fr.B, b * y56e0 s * b⁻¹ = κ * y56e0 s := by
  intro κ hκ
  obtain ⟨hv0B, hzB, -, -, -, hcases⟩ := y56_v0 hH
  have hb1B : s.fr.b₁ ∈ s.fr.B :=
    y56_mem_B_of_conj (s3_b₁_mem_S s) (y56_b1_conj_v0 hH)
  have hh0B : s.fr.h₀ ∈ s.fr.B :=
    y56_mem_B_of_conj (s3_h₀_mem_S s) (y56_h0_conj_v0 hH)
  have hb1h0B : s.fr.b₁ * s.fr.h₀ ∈ s.fr.B := by
    refine y56_mem_B_of_conj (mul_mem (s3_b₁_mem_S s) (s3_h₀_mem_S s)) ?_
    calc (s.fr.b₁ * s.fr.h₀) * (s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.h₀)⁻¹
        = s.fr.b₁ * (s.fr.h₀ * (s.fr.b₁ * s.fr.b₂) * s.fr.h₀⁻¹) * s.fr.b₁⁻¹ := by group
      _ = s.fr.b₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.b₁⁻¹ := by rw [y56_h0_conj_v0 hH]
      _ = s.fr.b₁ * s.fr.b₂ := y56_b1_conj_v0 hH
  rcases hcases κ hκ with h1 | hz | hv0 | hzv0
  · exact ⟨1, one_mem _, by rw [h1]; group⟩
  · exact ⟨s.fr.b₁, hb1B, by rw [hz]; exact y56_b1_conj_e0 hH⟩
  · exact ⟨s.fr.b₁ * s.fr.h₀, hb1h0B, by rw [hv0]; exact y56_b1h0_conj_e0 hH⟩
  · exact ⟨s.fr.h₀, hh0B, by rw [hzv0]; exact y56_h0_conj_e0 hH⟩

theorem y56_exists_y0 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : ∃ y₀ : G, IsY0 c.s y₀ := by
  have hwt : y56v0 c.s * c.s.t ∈ c.s.tCoset (cen c.s.fr.B) :=
    ⟨y56v0 c.s, (y56_v0 hH).1, rfl⟩
  rw [← y56_conjClass_C2 (s := c.s) (e := c.e) hH] at hwt
  obtain ⟨g, hgC2, hgt⟩ := hwt
  have he0E : y56e0 c.s ∈ c.s.fr.E := y56_e0_mem_E c.s
  have he0C2 : y56e0 c.s ∈ c.s.C₂ := y56_Q_le_C2 hH (Subgroup.mem_sup_left he0E)
  have hlamV : ⁅g, y56e0 c.s⁆ ∈ cen c.s.fr.B :=
    y56_C2_comm c hH g hgC2 (y56e0 c.s) he0C2
  obtain ⟨b, hbB, hbconj⟩ := y56_B_conj_e0 hH (⁅g, y56e0 c.s⁆) hlamV
  refine ⟨g * b, mul_mem hgC2 (y56_B_le_C2 hH hbB), ?_, ?_⟩
  · intro f hf
    obtain ⟨κ, hκ, hcase⟩ := y56_E_eq hH f hf
    have hgV : ∀ v ∈ cen c.s.fr.B, g * v * g⁻¹ = v :=
      fun v hv => y56_C2_cent_V hH g hgC2 v hv
    have hbV : ∀ v ∈ cen c.s.fr.B, b * v * b⁻¹ = v := by
      intro v hv
      have hvb : v ∈ Subgroup.centralizer (c.s.fr.B : Set G) := (Subgroup.mem_inf.mp hv).2
      have hcom : b * v = v * b := Subgroup.mem_centralizer_iff.mp hvb b hbB
      rw [hcom]; group
    have hy0V : (g * b) * κ * (g * b)⁻¹ = κ := by
      calc (g * b) * κ * (g * b)⁻¹ = g * (b * κ * b⁻¹) * g⁻¹ := by group
        _ = g * κ * g⁻¹ := by rw [hbV κ hκ]
        _ = κ := hgV κ hκ
    have hge0 : g * y56e0 c.s * g⁻¹ = (⁅g, y56e0 c.s⁆) * y56e0 c.s := by
      rw [commutatorElement_def]; group
    have hlam2 : ⁅g, y56e0 c.s⁆ * ⁅g, y56e0 c.s⁆ = 1 := by
      rw [← pow_two]
      exact y56_E_sq hH (⁅g, y56e0 c.s⁆) (y56_V_le_E hH hlamV)
    have hy0e0 : (g * b) * y56e0 c.s * (g * b)⁻¹ = y56e0 c.s := by
      calc (g * b) * y56e0 c.s * (g * b)⁻¹
          = g * (b * y56e0 c.s * b⁻¹) * g⁻¹ := by group
        _ = g * ((⁅g, y56e0 c.s⁆) * y56e0 c.s) * g⁻¹ := by rw [hbconj]
        _ = (g * ⁅g, y56e0 c.s⁆ * g⁻¹) * (g * y56e0 c.s * g⁻¹) := by group
        _ = ⁅g, y56e0 c.s⁆ * ((⁅g, y56e0 c.s⁆) * y56e0 c.s) := by
              rw [hgV (⁅g, y56e0 c.s⁆) hlamV, hge0]
        _ = ((⁅g, y56e0 c.s⁆) * ⁅g, y56e0 c.s⁆) * y56e0 c.s := by group
        _ = y56e0 c.s := by rw [hlam2, one_mul]
    rcases hcase with hcase | hcase
    · rw [hcase]; exact hy0V
    · rw [hcase]
      calc (g * b) * (κ * y56e0 c.s) * (g * b)⁻¹
          = ((g * b) * κ * (g * b)⁻¹) * ((g * b) * y56e0 c.s * (g * b)⁻¹) := by group
        _ = κ * y56e0 c.s := by rw [hy0V, hy0e0]
  · have hbt : b * c.s.t * b⁻¹ = c.s.t := by
      have hL : b ∈ L := s3_S_le_L c.s (s3_B_le_S c.s hbB)
      have h := s3_comm_t_of_mem_L (s := c.s) hL
      rw [h]; group
    calc (g * b) * c.s.t * (g * b)⁻¹ = g * (b * c.s.t * b⁻¹) * g⁻¹ := by group
      _ = g * c.s.t * g⁻¹ := by rw [hbt]
      _ = y56v0 c.s * c.s.t := hgt.symm

end CFSG.OddStandard.HigherRank.YamadaG23
