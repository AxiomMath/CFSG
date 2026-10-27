module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4T2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Q

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_cenT2_eq (c : Ctx4 s e) : cen s.T₂ = s.fr.Z := by
  have hzmem : s.fr.z ∈ cen s.T₂ := by
    refine Subgroup.mem_inf.mpr ⟨y4_z_mem_T2 s, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have h := f3_T2_fix_z c.toF33 y hy
    calc y * s.fr.z = (y * s.fr.z * y⁻¹) * y := by group
      _ = s.fr.z * y := by rw [h]
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hzmem)
  intro x hx
  obtain ⟨hxT2, hxcen⟩ := Subgroup.mem_inf.mp hx
  have ht_comm : x * s.t = s.t * x :=
    ((Subgroup.mem_centralizer_iff.mp hxcen) s.t (y4_t_mem_T2 s)).symm
  have hxT : x ∈ s.T := y4_T2_comm_t c hxT2 ht_comm
  have hxcenT : x ∈ cen s.T :=
    Subgroup.mem_inf.mpr ⟨hxT, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hxcen) y (y4_T_le_T2 s hy)⟩
  have hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t := s3_Q_eq s c.hS c.hZ c.hOut
  have hcenTeq : cen s.T = zt s := s3_cen_T_eq s c.hS c.hZ c.hOut hQ
  have hxzt : x ∈ zt s := hcenTeq ▸ hxcenT
  obtain ⟨x₁, hx1C2, -, hψ1, -⟩ := y4_exists_psi c
  have hx1T2 : x₁ ∈ s.T₂ := y4_C2_le_T2 s hx1C2
  have hx1x : x₁ * x = x * x₁ := (Subgroup.mem_centralizer_iff.mp hxcen) x₁ hx1T2
  have hconj : x₁ * x * x₁⁻¹ = x := by rw [hx1x]; group
  have hzconj : x₁ * s.fr.z * x₁⁻¹ = s.fr.z := y4_C2_cent_V c hx1C2 (y4_z_mem_V c)
  rcases (s3_mem_zt_iff s c.hA).mp hxzt with rfl | rfl | rfl | rfl
  · rw [SFrame.Z]; exact Subgroup.one_mem _
  · rw [SFrame.Z]; exact Subgroup.mem_zpowers _
  · have ht : ⁅x₁, s.t⁆ * s.t = s.t := by
      rw [← y4_conj_t]; exact hconj
    exact absurd (mul_right_cancel (show ⁅x₁, s.t⁆ * s.t = 1 * s.t by rw [ht, one_mul])) hψ1
  · have hL : x₁ * (s.fr.z * s.t) * x₁⁻¹ = s.fr.z * (⁅x₁, s.t⁆ * s.t) := by
      calc x₁ * (s.fr.z * s.t) * x₁⁻¹
          = (x₁ * s.fr.z * x₁⁻¹) * (x₁ * s.t * x₁⁻¹) := by group
        _ = s.fr.z * (⁅x₁, s.t⁆ * s.t) := by rw [hzconj, y4_conj_t]
    have h2 : s.fr.z * (⁅x₁, s.t⁆ * s.t) = s.fr.z * s.t := by rw [← hL]; exact hconj
    have ht : ⁅x₁, s.t⁆ * s.t = s.t := mul_left_cancel h2
    exact absurd (mul_right_cancel (show ⁅x₁, s.t⁆ * s.t = 1 * s.t by rw [ht, one_mul])) hψ1

theorem y4_normIn_zt (c : Ctx4 s e) : normIn s.T₂ (zt s) = e.T₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t := s3_Q_eq s c.hS c.hZ c.hOut
  have hcenR : cen s.R = zt s := s3_cen_R_eq s c.hS c.hZ hQ
  have hT1Q : e.T₁ ≤ normIn s.T₂ (zt s) := by
    refine le_inf (f3_c8 c.toF33) ?_
    rw [← hcenR]
    exact e.sylow.1
  symm
  refine sylowIn_eq_of_le (V := normalizer (cen s.R : Set G)) (P := e.T₁)
    (Q := normIn s.T₂ (zt s)) e.sylow ((y4_T2_isPGroup c).to_le inf_le_left) ?_ hT1Q
  intro x hx
  have hxz : x ∈ normalizer (zt s : Set G) := (Subgroup.mem_inf.mp hx).2
  rwa [← hcenR] at hxz

theorem y4_Z2_le_T1 (c : Ctx4 s e) : zSeries 2 s.T₂ ≤ e.T₁ := by
  intro x hx
  obtain ⟨hxT2, hxcomm⟩ := (y4_mem_zSeries_succ 1 s.T₂ x).mp hx
  have hψZ : ⁅x, s.t⁆ ∈ s.fr.Z := by
    have h := hxcomm s.t (y4_t_mem_T2 s)
    rwa [y4_zSeries_one, y4_cenT2_eq c] at h
  have hψzt : ⁅x, s.t⁆ ∈ zt s := by
    change ⁅x, s.t⁆ ∈ zpowers s.fr.z at hψZ
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hψZ
  have hzconj : x * s.fr.z * x⁻¹ = s.fr.z := f3_T2_fix_z c.toF33 x hxT2
  have hz_zt : s.fr.z ∈ zt s := Subgroup.subset_closure (by simp)
  have ht_zt : s.t ∈ zt s := Subgroup.subset_closure (by simp)
  have hnorm : x ∈ normalizer (zt s : Set G) := by
    refine y4_mem_normalizer_of_conj_mem ?_
    intro u hu
    rcases (s3_mem_zt_iff s c.hA).mp hu with rfl | rfl | rfl | rfl
    · simpa using Subgroup.one_mem (zt s)
    · rw [hzconj]; exact hz_zt
    · rw [y4_conj_t]; exact Subgroup.mul_mem _ hψzt ht_zt
    · have hL : x * (s.fr.z * s.t) * x⁻¹ = s.fr.z * (⁅x, s.t⁆ * s.t) := by
        calc x * (s.fr.z * s.t) * x⁻¹
            = (x * s.fr.z * x⁻¹) * (x * s.t * x⁻¹) := by group
          _ = s.fr.z * (⁅x, s.t⁆ * s.t) := by rw [hzconj, y4_conj_t]
      rw [hL]
      exact Subgroup.mul_mem _ hz_zt (Subgroup.mul_mem _ hψzt ht_zt)
  have hxQ : x ∈ normIn s.T₂ (zt s) := Subgroup.mem_inf.mpr ⟨hxT2, hnorm⟩
  exact (y4_normIn_zt c) ▸ hxQ

end CFSG.OddStandard.HigherRank.YamadaG23
