module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Cover
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52N0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Dihed

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y52_excl_data {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    (hu : c.g * c.d ∈ c.s.C₂) :
    ∃ v v' : G, v ∈ c.s.C₂ ∧ v' ∈ c.s.C₂ ∧
      (c.g * c.d) * (c.g * c.d) = 1 ∧ v * v = 1 ∧ v' * v' = 1 ∧
      (∀ x ∈ c.s.C₂, ∃ p ∈ f3P c.s, x = p ∨ x = p * (c.g * c.d) ∨ x = p * v ∨ x = p * v') ∧
      (c.g * c.d) * v * v' ∈ f3P c.s ∧
      y5a c.s * (c.g * c.d) * (y5a c.s)⁻¹ = y52b c.s * (c.g * c.d) ∧
      y5a c.s * v * (y5a c.s)⁻¹ * v'⁻¹ ∈ f3P c.s ∧
      y5a c.s * v' * (y5a c.s)⁻¹ * v⁻¹ ∈ f3P c.s := by
  obtain ⟨k, hk⟩ := y52_exists_K hH
  obtain ⟨hgT, -, hgact, hg2, hgd⟩ := c.g_spec hRT
  have hd2 : c.d ^ 2 = 1 := y5_d_sq c
  have hgd' : c.g * c.d = c.d * c.g := mul_inv_eq_iff_eq_mul.mp hgd
  have hgt : c.g * c.s.t = c.s.t * c.g := s3_comm_t_of_mem_T c.s hgT
  have hgt' : c.g * c.s.t * c.g⁻¹ = c.s.t := by rw [hgt]; group
  have hgz : c.g * c.s.fr.z * c.g⁻¹ = c.s.fr.z := (y5_g_swap hH hg2 hgact).2.2.2.2.1
  have hdtd : c.d * c.s.t * c.d⁻¹ = c.s.fr.z * c.s.t := y5_dtd hH
  have hu2 : (c.g * c.d) * (c.g * c.d) = 1 := by
    calc (c.g * c.d) * (c.g * c.d) = c.g * (c.d * c.g) * c.d := by group
      _ = c.g * (c.g * c.d) * c.d := by rw [← hgd']
      _ = (c.g * c.g) * (c.d * c.d) := by group
      _ = 1 := by rw [← pow_two, ← pow_two, hg2, hd2, one_mul]
  have hphi : f3phi c.s (c.g * c.d) = c.s.fr.z := by
    unfold f3phi
    calc (c.g * c.d) * c.s.t * (c.g * c.d)⁻¹ * c.s.t⁻¹
        = c.g * (c.d * c.s.t * c.d⁻¹) * c.g⁻¹ * c.s.t⁻¹ := by group
      _ = c.g * (c.s.fr.z * c.s.t) * c.g⁻¹ * c.s.t⁻¹ := by rw [hdtd]
      _ = (c.g * c.s.fr.z * c.g⁻¹) * (c.g * c.s.t * c.g⁻¹) * c.s.t⁻¹ := by group
      _ = c.s.fr.z * c.s.t * c.s.t⁻¹ := by rw [hgz, hgt']
      _ = c.s.fr.z := by group
  have hzne : c.s.fr.z ≠ 1 := by
    intro h
    have h1 : orderOf c.s.fr.z = 1 := by rw [h, orderOf_one]
    rw [s3_z_order c.s (lfactsA_of_setting hH.hS hH.hZ c.s)] at h1
    norm_num at h1
  have huP : c.g * c.d ∉ f3P c.s := by
    intro hmem
    have hX0 : c.g * c.d ∈ f3X0 c.s := f3_P_le_X0 c.s hmem
    have hY : c.g * c.d ∈ f3Y c.s := f3_C₂_le_Y hH hu
    have h1 : f3phi c.s (c.g * c.d) = 1 := (f3_phi_eq_one hH (c.g * c.d) hY).mpr hX0
    rw [hphi] at h1
    exact hzne h1
  have hkX : k ∈ c.s.X :=
    f3_N_le_X c.s ⟨s3_L_le_H c.s hH.hS (Subgroup.mem_inf.mp hk.mem).1,
      (Subgroup.mem_inf.mp hk.mem).2⟩
  have hk2X : k ^ 2 ∈ c.s.X := Subgroup.pow_mem c.s.X hkX 2
  have hvC : k * (c.g * c.d) * k⁻¹ ∈ c.s.C₂ := f3_C₂_normal hH k hkX _ hu
  have hvC' : k ^ 2 * (c.g * c.d) * (k ^ 2)⁻¹ ∈ c.s.C₂ :=
    f3_C₂_normal hH (k ^ 2) hk2X _ hu
  have hv2 : (k * (c.g * c.d) * k⁻¹) * (k * (c.g * c.d) * k⁻¹) = 1 := by
    calc k * (c.g * c.d) * k⁻¹ * (k * (c.g * c.d) * k⁻¹)
        = k * ((c.g * c.d) * (c.g * c.d)) * k⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hv2' : (k ^ 2 * (c.g * c.d) * (k ^ 2)⁻¹) * (k ^ 2 * (c.g * c.d) * (k ^ 2)⁻¹) = 1 := by
    calc k ^ 2 * (c.g * c.d) * (k ^ 2)⁻¹ * (k ^ 2 * (c.g * c.d) * (k ^ 2)⁻¹)
        = k ^ 2 * ((c.g * c.d) * (c.g * c.d)) * (k ^ 2)⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have had : y5a c.s * c.d * (y5a c.s)⁻¹ = c.d := by
    have hda : c.d * y5a c.s = y5a c.s * c.d :=
      mul_inv_eq_iff_eq_mul.mp (y5_d_cent_A c (y5a c.s) (y5a_mem_A c.s))
    rw [← hda]; group
  have hag : y5a c.s * c.g * (y5a c.s)⁻¹ = y52b c.s * c.g := by
    have h : y5a c.s * c.g * (y5a c.s)⁻¹ = ⁅y5a c.s, c.g⁆ * c.g := by
      rw [commutatorElement_def]; group
    rw [h, y5_comm_a_g hH hg2 hgact]
  have hau : y5a c.s * (c.g * c.d) * (y5a c.s)⁻¹ = y52b c.s * (c.g * c.d) := by
    calc y5a c.s * (c.g * c.d) * (y5a c.s)⁻¹
        = (y5a c.s * c.g * (y5a c.s)⁻¹) * (y5a c.s * c.d * (y5a c.s)⁻¹) := by group
      _ = y52b c.s * (c.g * c.d) := by rw [hag, had]; group
  have haswap := y52_a_swap (y := c.g * c.d) hH hk hu hphi
  refine ⟨k * (c.g * c.d) * k⁻¹, k ^ 2 * (c.g * c.d) * (k ^ 2)⁻¹,
    hvC, hvC', hu2, hv2, hv2', ?_, ?_, hau, haswap.1, haswap.2⟩
  · exact y52_cover (y := c.g * c.d) hH hk hu huP
  · exact y52_cover_prod (y := c.g * c.d) hH hk hu huP

end CFSG.OddStandard.HigherRank.YamadaG23
