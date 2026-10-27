module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8f

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M4_le_M7_of_ne (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    M4 c.e ≤ M7 c.s := by
  by_contra hbad
  obtain ⟨m, hm4, hu1M7, hu1CS3, hu1t⟩ := y7b_exists_u1 c hb hRT hbad
  obtain ⟨x, hxM7, hxCS3, hxCS5, hxt⟩ := y7b_exists_x c hb hRT
  have hM7X7 : M7 c.s ≤ X7 c.s := (y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb)
  obtain ⟨e₁, he₁, m₁, hm₁, hx_eq⟩ := y7b_cs3_X7 c hb (hM7X7 hxM7) hxCS3
  obtain ⟨e₂, he₂, m₂, hm₂, hu_eq⟩ := y7b_cs3_X7 c hb (hM7X7 hu1M7) hu1CS3
  have he₁' : e₁ ∉ M3 c.s := by
    intro h
    exact hxt (by rw [hx_eq]; exact (M3 c.s).mul_mem h hm₁)
  have he₂' : e₂ ∉ M3 c.s := by
    intro h
    exact hu1t (by rw [hu_eq]; exact (M3 c.s).mul_mem h hm₂)
  have htheta : (⁅x, c.s.t⁆)⁻¹ * ⁅m * c.g, c.s.t⁆ ∈ M3 c.s := by
    have he12 : e₁⁻¹ * e₂ ∈ M3 c.s := y7b_E_quot c hb he₁ he₁' he₂ he₂'
    rw [hx_eq, hu_eq]
    have hgrp : (e₁ * m₁)⁻¹ * (e₂ * m₂) = m₁⁻¹ * (e₁⁻¹ * e₂) * m₂ := by group
    rw [hgrp]
    exact (M3 c.s).mul_mem ((M3 c.s).mul_mem ((M3 c.s).inv_mem hm₁) he12) hm₂
  have hyBM : x * (m * c.g)⁻¹ ∈ y7bBM c.s := y7b_theta_eq c hb hxM7 hu1M7 htheta
  have hyCS3 : x * (m * c.g)⁻¹ ∈ y7bCS3 c :=
    (y7bCS3 c).mul_mem hxCS3 ((y7bCS3 c).inv_mem hu1CS3)
  obtain ⟨e, heE, m', hm'M3, hy_eq⟩ := y7b_cs3_BM c hb hyBM hyCS3
  have hmM5 : m ∈ M5 c.e := by
    unfold M5; exact Subgroup.mem_sup_right hm4
  have hmM6 : m ∈ M6 c.e := y7b_M5_le_M6 c hb hmM5
  have hyM5 : x * (m * c.g)⁻¹ ∈ M5 c.e := by
    rw [hy_eq]
    unfold M5
    exact (M3 c.s ⊔ M4 c.e).mul_mem (Subgroup.mem_sup_right (y7b_E_le_M4 c hb heE))
      (Subgroup.mem_sup_left hm'M3)
  have hyCS5 : x * (m * c.g)⁻¹ ∈ y7bCS5 c :=
    y7b_M6_le_CS5 c hb (y7b_M5_le_M6 c hb hyM5)
  have hu1CS5 : m * c.g ∈ y7bCS5 c := by
    have h : (x * (m * c.g)⁻¹)⁻¹ * x ∈ y7bCS5 c :=
      (y7bCS5 c).mul_mem ((y7bCS5 c).inv_mem hyCS5) hxCS5
    rwa [show (x * (m * c.g)⁻¹)⁻¹ * x = m * c.g by group] at h
  have he0E : c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂ ∈ c.s.fr.E := y56_e0_mem_E c.s
  have he0M5 : c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂ ∈ M5 c.e := by
    unfold M5; exact Subgroup.mem_sup_right (y7b_E_le_M4 c hb he0E)
  have he0M6 : c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂ ∈ M6 c.e :=
    y7b_M5_le_M6 c hb he0M5
  have hcomm : ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m * c.g⁆ ∈ V1 c.e :=
    hu1CS5.2.2 _ he0M5
  have hcm : ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m⁆ ∈ V1 c.e :=
    (y7b_M6_comm_sq c hb).1 _ he0M6 m hmM6
  have hV1M6 : V1 c.e ≤ M6 c.e :=
    (y7b_V1_le_M4 c hb).trans
      ((show M4 c.e ≤ M5 c.e from le_sup_right).trans (y7b_M5_le_M6 c hb))
  have hcomm_eq : ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m * c.g⁆ =
      ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m⁆ *
        (m * ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ * m⁻¹) := by
    simp only [commutatorElement_def]; group
  have hwV1 : m * ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ * m⁻¹ ∈ V1 c.e := by
    have h := hcomm
    rw [hcomm_eq] at h
    have h2 : (⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m⁆)⁻¹ *
        (⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m⁆ *
          (m * ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ * m⁻¹)) ∈ V1 c.e :=
      (V1 c.e).mul_mem ((V1 c.e).inv_mem hcm) h
    rwa [show (⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m⁆)⁻¹ *
        (⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, m⁆ *
          (m * ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ * m⁻¹)) =
        m * ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ * m⁻¹ by group] at h2
  have hvV1 : ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ ∈ V1 c.e := by
    have h := y7b_norm_of_V1_le c hb (N := V1 c.e) le_rfl hV1M6 m⁻¹ (inv_mem hmM6)
      (m * ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ * m⁻¹) hwV1
    rwa [show m⁻¹ * (m * ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ * m⁻¹) * (m⁻¹)⁻¹ =
        ⁅c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂, c.g⁆ by group] at h
  exact y7b_g_comm_e0_not_mem_V1 c hb hRT (by
    rw [← commutatorElement_inv]
    exact (V1 c.e).inv_mem hvV1)

end CFSG.OddStandard.HigherRank.YamadaG23
