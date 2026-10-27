module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Conf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem mem_normalizer_inf_of_subgroupOf {G : Type*} [Group G] {M Q : Subgroup G} {g : M}
    (hg : g ∈ normalizer ((Q.subgroupOf M : Subgroup M) : Set M)) :
    (g : G) ∈ normalizer ((Q ⊓ M : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ M
  · have h1 := (mem_normalizer_iff.mp hg) ⟨y, hy⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [mem_inf, mem_inf]
    exact ⟨fun h2 => ⟨h1.mp h2.1, mul_mem (mul_mem g.2 hy) (inv_mem g.2)⟩,
      fun h2 => ⟨h1.mpr h2.1, hy⟩⟩
  · have h2 : (g : G) * y * (g : G)⁻¹ ∉ M := by
      intro h3
      apply hy
      have := mul_mem (mul_mem (inv_mem g.2) h3) g.2
      rwa [show (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g = y by group] at this
    exact ⟨fun h3 => absurd h3.2 hy, fun h3 => absurd h3.2 h2⟩

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

structure Q3Data (H : L83Hyp h) where
  b : X
  g : X
  z : X
  RM : Subgroup X
  c : Cat8.Q3Conf (h.K ⧸ pPrimeCore 2 h.K)
  b_ord : orderOf b = 2
  B_eq : h.B = zpowers b
  P_eq : h.P = h.T
  P_mem : ∀ w ∈ h.P, w = 1 ∨ w = h.a ∨ w = b ∨ w = h.a * b
  ba : b * h.a = h.a * b
  xbx : h.x⁻¹ * b * h.x = h.a * b
  xbx' : h.x * b * h.x⁻¹ = h.a * b
  normalizer_B : normalizer (h.B : Set X) = centralizer ({b} : Set X)
  Q_eq : h.Q = h.S ⊓ centralizer ({b} : Set X)
  index_Q : ((centralizer ({b} : Set X)).subgroupOf h.S).index = 2
  g_M : g ∈ h.M3
  g_K : g ∈ h.K
  g_norm : g ∈ normalizer ((h.Q ⊓ h.M3 : Subgroup X) : Set X)
  g_not_mem : g ∉ h.Q
  g_sq : g * g ∈ h.Q
  tau_K : h.a * (g⁻¹ * h.a * g) ∈ h.K
  z_D : z ∈ h.D
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_comm : ∀ d ∈ h.D, z * d = d * z
  RM_le : RM ≤ h.M3
  RM_sylow : ∃ T : Sylow 2 ↥h.M3, (T : Subgroup _) = RM.subgroupOf h.M3
  Q1g_le : (h.Q ⊓ h.M3) ⊔ zpowers g ≤ RM
  c_props : c.Props
  c_a : c.a = H.rhoA
  c_Q : c.Q = (h.Q.subgroupOf h.M3).map H.rho
  c_g : c.g = H.rho ⟨g, g_M⟩
  c_R : c.R = (RM.subgroupOf h.M3).map H.rho
  c_z : c.z = H.rho ⟨z, H.D_le_M3 z_D⟩

variable (H : L83Hyp h)
include H

theorem exists_Q3Data (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) (hF2 : CFQ3F2) (hL0 : CFQ3L0) (hConf : CFQ3Conf) : Nonempty (Q3Data H) := by
  obtain ⟨b, hb2, hBb, hPT, hPmem, hba, hxbx, hxbx', hNB, hQb, hidx⟩ :=
    h.sec8_P4_setup H.T_eq H.C_eq H.card_P H.x_mul_x
  obtain ⟨g, z, hzD, RM, c, hgK, hgN, hgQ, hgsq, htau, hz2, hz1, hzc, hRM, ⟨T, hT⟩, hca, hcQ,
    hcg, hcR, hcz⟩ := H.exists_conf hq hCF1 hCF2 hOut hF2 hL0
  refine ⟨{
    b := b
    g := (g : X)
    z := z
    RM := RM.map h.M3.subtype
    c := c
    b_ord := hb2
    B_eq := hBb
    P_eq := hPT
    P_mem := hPmem
    ba := hba
    xbx := hxbx'
    xbx' := hxbx
    normalizer_B := hNB
    Q_eq := hQb
    index_Q := hidx
    g_M := g.2
    g_K := hgK
    g_norm := ?_
    g_not_mem := fun h1 => hgQ h1
    g_sq := hgsq
    tau_K := htau
    z_D := hzD
    z_sq := hz2
    z_ne := hz1
    z_comm := hzc
    RM_le := map_subtype_le _
    RM_sylow := ⟨T, by
      rw [hT]
      exact (comap_map_eq_self_of_injective h.M3.subtype_injective _).symm⟩
    Q1g_le := ?_
    c_props := hConf _ hq.1 c
    c_a := hca
    c_Q := hcQ
    c_g := hcg
    c_R := by
      rw [hcR]
      congr 1
      exact (comap_map_eq_self_of_injective h.M3.subtype_injective RM).symm
    c_z := hcz }⟩
  · exact mem_normalizer_inf_of_subgroupOf hgN
  · have := map_mono (f := h.M3.subtype) hRM
    rwa [Subgroup.map_sup, subgroupOf_map_subtype, MonoidHom.map_zpowers] at this

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
