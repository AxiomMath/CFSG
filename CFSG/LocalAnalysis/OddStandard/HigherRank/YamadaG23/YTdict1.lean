module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setup
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSetBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_L_le_H (hS : HRSetting G L) : L ≤ s.H :=
  (Setup.normal_centralizer hS s.t_mem s.t_order).1

theorem s3_L_normal_H (hS : HRSetting G L) : (L.subgroupOf s.H).Normal :=
  (Setup.normal_centralizer hS s.t_mem s.t_order).2.1

theorem s3_H_le_N (hS : HRSetting G L) : s.H ≤ normalizer (L : Set G) :=
  (Setup.normal_centralizer hS s.t_mem s.t_order).2.2

theorem s3_T_le_N (hS : HRSetting G L) : s.T ≤ normalizer (L : Set G) :=
  s.sylow_T.1.trans (s3_H_le_N s hS)

theorem s3_M_le_H (hS : HRSetting G L) : L ⊔ centIn s.H L ≤ s.H :=
  sup_le (s3_L_le_H s hS) inf_le_left

theorem s3_M_normal_H (hS : HRSetting G L) : ((L ⊔ centIn s.H L).subgroupOf s.H).Normal := by
  have hM : L ⊔ centIn s.H L ≤ s.H := s3_M_le_H s hS
  rw [Subgroup.normal_subgroupOf_iff hM]
  intro m k hm hk
  have hkL : k ∈ normalizer (L : Set G) := s3_H_le_N s hS hk
  have hLmap : L.map (MulAut.conj k) = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hkL
  have hCmap : (centIn s.H L).map (MulAut.conj k) ≤ centIn s.H L := by
    rintro x ⟨c, hc, rfl⟩
    rcases Subgroup.mem_inf.mp hc with ⟨hcH, hcC⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact s.H.mul_mem (s.H.mul_mem hk hcH) (s.H.inv_mem hk)
    · rw [Subgroup.mem_centralizer_iff] at hcC ⊢
      intro l hl
      have hkl : k⁻¹ * l * k ∈ L :=
        (Subgroup.mem_set_normalizer_iff''.mp hkL l).mp hl
      calc l * (k * c * k⁻¹)
          = k * ((k⁻¹ * l * k) * c) * k⁻¹ := by group
        _ = k * (c * (k⁻¹ * l * k)) * k⁻¹ := by rw [hcC (k⁻¹ * l * k) hkl]
        _ = (k * c * k⁻¹) * l := by group
  have hMmap : (L ⊔ centIn s.H L).map (MulAut.conj k) ≤ L ⊔ centIn s.H L := by
    rw [Subgroup.map_sup]
    exact sup_le (hLmap.le.trans le_sup_left) (hCmap.trans le_sup_right)
  exact hMmap (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)

theorem s3_R_eq (hS : HRSetting G L) : s.R = s.T ⊓ (L ⊔ centIn s.H L) :=
  sylowIn_eq_of_le (V := L ⊔ centIn s.H L) (P := s.R) (Q := s.T ⊓ (L ⊔ centIn s.H L))
    s.sylow_R s.sylow_T.2.1.to_inf_left inf_le_right (le_inf s.R_le_T s.sylow_R.1)

theorem s3_R_normal_T (hS : HRSetting G L) : (s.R.subgroupOf s.T).Normal := by
  have hT : s.T ≤ s.H := s.sylow_T.1
  rw [s3_R_eq s hS, Subgroup.inf_subgroupOf_left]
  rw [← Subgroup.comap_inclusion_subgroupOf hT (L ⊔ centIn s.H L)]
  exact (s3_M_normal_H s hS).comap (Subgroup.inclusion hT)

theorem s3_R_inf_L : s.R ⊓ L = s.fr.S :=
  (sylowIn_eq_of_le (V := L) (P := s.fr.S) (Q := s.R ⊓ L)
    s.sylow_S s.sylow_R.2.1.to_inf_left inf_le_right
    (le_inf s.S_le_R s.sylow_S.1)).symm

theorem s3_S_normal_T (hS : HRSetting G L) : (s.fr.S.subgroupOf s.T).Normal := by
  have hT : s.T ≤ s.H := s.sylow_T.1
  have hL : (L.subgroupOf s.T).Normal := by
    rw [← Subgroup.comap_inclusion_subgroupOf hT L]
    exact (s3_L_normal_H s hS).comap (Subgroup.inclusion hT)
  have hR : (s.R.subgroupOf s.T).Normal := s3_R_normal_T s hS
  have hsplit : (s.fr.S.subgroupOf s.T) = (s.R.subgroupOf s.T) ⊓ (L.subgroupOf s.T) := by
    rw [← s3_R_inf_L s]
    simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
  rw [hsplit]
  haveI := hR
  haveI := hL
  exact Subgroup.normal_inf_normal _ _

theorem s3_T_inf_centralizer (h31 : s.Fact31) : s.T ⊓ centralizer (L : Set G) = zpowers s.t :=
  (sylowIn_eq_of_le (V := centralizer (L : Set G)) (P := zpowers s.t)
    (Q := s.T ⊓ centralizer (L : Set G)) h31.1 s.sylow_T.2.1.to_inf_left inf_le_right
    (le_inf (Subgroup.zpowers_le.mpr (s3_t_mem_T s)) (Subgroup.zpowers_le.mpr s.t_mem))).symm

theorem s3_jSub_R : jSub L s.R = s.fr'.S := by
  have hRmem : s.R ≤ L ⊔ centralizer (L : Set G) :=
    s.sylow_R.1.trans (sup_le_sup_left inf_le_right L)
  have hInner : jSub L s.R ≤ innerAut (L ⧸ center L) := jSub_le_inner L hRmem
  have hP : IsPGroup 2 (jSub L s.R) := isPGroup_jSub L s.sylow_R.2.1
  have hle : s.fr'.S ≤ jSub L s.R := by
    rw [← s3_jSub_S s]
    exact jSub_mono L s.S_le_R
  exact (sylowIn_eq_of_le (V := innerAut (L ⧸ center L)) (P := s.fr'.S) (Q := jSub L s.R)
    s.facts.1.2.1 hP hInner hle).symm

end CFSG.OddStandard.HigherRank.YamadaG23
