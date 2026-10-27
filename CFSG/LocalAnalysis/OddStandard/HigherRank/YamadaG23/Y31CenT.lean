module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

private theorem comm_of_eq_mul_inv {G : Type} [Group G] {x y q w : G} (hy : y = x * q⁻¹)
    (hxw : w * x = x * w) (hqw : q⁻¹ * w = w * q⁻¹) : w * y = y * w := by
  rw [hy]
  calc w * (x * q⁻¹) = (w * x) * q⁻¹ := by group
    _ = (x * w) * q⁻¹ := by rw [hxw]
    _ = x * (w * q⁻¹) := by group
    _ = x * (q⁻¹ * w) := by rw [← hqw]
    _ = (x * q⁻¹) * w := by group

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_Q_le_R (hS : HRSetting G L) : s.T ⊓ centralizer (L : Set G) ≤ s.R := by
  intro q hq
  obtain ⟨hqT, hqC⟩ := Subgroup.mem_inf.mp hq
  rw [s3_R_eq s hS]
  exact Subgroup.mem_inf.mpr
    ⟨hqT, Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨s.sylow_T.1 hqT, hqC⟩)⟩

theorem s3_S_inf_cent (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) :
    ∀ x ∈ s.fr.S, x ∈ centralizer (L : Set G) → x = 1 := by
  intro x hxS hxC
  exact s3_inj_on_S s hS hZ hxS (Subgroup.one_mem s.fr.S)
    (actsAs_of_mem_centralizer L hxC) (actsAs_one L)

theorem s3_R_eq_SQ (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) :
    ∀ r ∈ s.R, ∃ x ∈ s.fr.S, ∃ q ∈ s.T ⊓ centralizer (L : Set G), r = x * q := by
  intro r hr
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have hT : s.T ≤ normalizer (L : Set G) := s3_T_le_N s hS
  have hrT : r ∈ s.T := s.R_le_T hr
  have hjR : jOn L hT ⟨r, hrT⟩ ∈ jSub L s.R :=
    (mem_jSub L).mpr ⟨r, hr, jOn_actsAs L hT ⟨r, hrT⟩⟩
  rw [s3_jSub_R s] at hjR
  rw [← s3_jSub_S s] at hjR
  obtain ⟨x, hxS, hax⟩ := (mem_jSub L).mp hjR
  have hxT : x ∈ s.T := s3_S_le_T s hxS
  have hqT : x⁻¹ * r ∈ s.T := Subgroup.mul_mem _ (Subgroup.inv_mem _ hxT) hrT
  have hqActs : ActsAs L (x⁻¹ * r) 1 := by
    have h2 : ActsAs L (x⁻¹ * r) ((jOn L hT ⟨r, hrT⟩)⁻¹ * jOn L hT ⟨r, hrT⟩) :=
      actsAs_mul L (actsAs_inv L hax) (jOn_actsAs L hT ⟨r, hrT⟩)
    simpa using h2
  have hqC : x⁻¹ * r ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hqActs
  exact ⟨x, hxS, x⁻¹ * r, Subgroup.mem_inf.mpr ⟨hqT, hqC⟩, by group⟩

theorem s3_cen_T_le_R (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) : cen s.T ≤ s.R := by
  by_cases hRT : s.R = s.T
  · rw [hRT]
    exact inf_le_left
  · intro c hc
    haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
    obtain ⟨hcT, hccent⟩ := Subgroup.mem_inf.mp hc
    have hT : s.T ≤ normalizer (L : Set G) := s3_T_le_N s hS
    let jc : MulAut (L ⧸ center L) := jOn L hT ⟨c, hcT⟩
    have hjcT : jc ∈ jSub L s.T :=
      (mem_jSub L).mpr ⟨c, hcT, jOn_actsAs L hT ⟨c, hcT⟩⟩
    have hjcSσ : jc ∈ s.fr'.Sσ := by
      rwa [s3_jSub_T s hS hOut hRT] at hjcT
    have hjccen : jc ∈ centralizer (s.fr'.Sσ : Set (MulAut (L ⧸ center L))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro β hβ
      rw [← s3_jSub_T s hS hOut hRT] at hβ
      obtain ⟨y, hyT, hyβ⟩ := (mem_jSub L).mp hβ
      have hcy : c * y = y * c := ((Subgroup.mem_centralizer_iff.mp hccent) y hyT).symm
      have h1 : ActsAs L (c * y) (jc * β) :=
        actsAs_mul L (jOn_actsAs L hT ⟨c, hcT⟩) hyβ
      have h2 : ActsAs L (c * y) (β * jc) := by
        rw [hcy]
        exact actsAs_mul L hyβ (jOn_actsAs L hT ⟨c, hcT⟩)
      exact (actsAs_unique L h1 h2).symm
    have hjcCen : jc ∈ cen s.fr'.Sσ := Subgroup.mem_inf.mpr ⟨hjcSσ, hjccen⟩
    have hjcZ : jc ∈ s.fr'.Z := by
      rwa [s.facts.2.2.2.2.1.1.1] at hjcCen
    rw [← s3_jSub_Z s] at hjcZ
    obtain ⟨w, hwZ, hw⟩ := (mem_jSub L).mp hjcZ
    have hZS : s.fr.Z ≤ s.fr.S := by
      rw [SFrame.Z]
      exact Subgroup.zpowers_le.mpr (s3_A_le_S s (s3_z_mem_A s))
    have hwS : w ∈ s.fr.S := hZS hwZ
    have hwT : w ∈ s.T := s3_S_le_T s hwS
    have hqT : w⁻¹ * c ∈ s.T := Subgroup.mul_mem _ (Subgroup.inv_mem _ hwT) hcT
    have hqActs : ActsAs L (w⁻¹ * c) 1 := by
      have h2 : ActsAs L (w⁻¹ * c) (jc⁻¹ * jc) :=
        actsAs_mul L (actsAs_inv L hw) (jOn_actsAs L hT ⟨c, hcT⟩)
      simpa using h2
    have hqC : w⁻¹ * c ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hqActs
    have hqR : w⁻¹ * c ∈ s.R := s3_Q_le_R s hS (Subgroup.mem_inf.mpr ⟨hqT, hqC⟩)
    have hwR : w ∈ s.R := s.S_le_R hwS
    have hmem : w * (w⁻¹ * c) ∈ s.R := Subgroup.mul_mem _ hwR hqR
    rwa [mul_inv_cancel_left] at hmem

theorem s3_cen_T_le (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) :
    ∀ x ∈ cen s.T, ∃ k : ℤ, ∃ q ∈ s.T ⊓ centralizer (L : Set G), x = s.fr.z ^ k * q := by
  intro x hx
  have hxR : x ∈ s.R := s3_cen_T_le_R s hS hZ hOut hx
  obtain ⟨y, hyS, q, hqQ, hxyq⟩ := s3_R_eq_SQ s hS hZ x hxR
  have hA : LFactsA s := lfactsA_of_setting hS hZ s
  have hy_eq : y = x * q⁻¹ := by rw [hxyq]; group
  have hxcent : x ∈ centralizer (s.T : Set G) := (Subgroup.mem_inf.mp hx).2
  have hqC : q ∈ centralizer (L : Set G) := (Subgroup.mem_inf.mp hqQ).2
  have hycen : y ∈ cen s.fr.S := by
    refine Subgroup.mem_inf.mpr ⟨hyS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hxw : w * x = x * w :=
      (Subgroup.mem_centralizer_iff.mp hxcent) w (s3_S_le_T s hw)
    have hqw : q⁻¹ * w = w * q⁻¹ :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hqC)) w (s3_S_le_L s hw)).symm
    exact comm_of_eq_mul_inv hy_eq hxw hqw
  have hyZ : y ∈ s.fr.Z := by
    have h := hycen
    rwa [s3_cen_S s hA] at h
  rw [SFrame.Z] at hyZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyZ
  exact ⟨k, q, hqQ, by rw [hxyq, hk]⟩

theorem s3_cen_R_le (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) :
    ∀ x ∈ cen s.R, ∃ k : ℤ, ∃ q ∈ s.T ⊓ centralizer (L : Set G), x = s.fr.z ^ k * q := by
  intro x hx
  obtain ⟨hxR, hxcent⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hyS, q, hqQ, hxyq⟩ := s3_R_eq_SQ s hS hZ x hxR
  have hA : LFactsA s := lfactsA_of_setting hS hZ s
  have hy_eq : y = x * q⁻¹ := by rw [hxyq]; group
  have hqC : q ∈ centralizer (L : Set G) := (Subgroup.mem_inf.mp hqQ).2
  have hycen : y ∈ cen s.fr.S := by
    refine Subgroup.mem_inf.mpr ⟨hyS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hxw : w * x = x * w :=
      (Subgroup.mem_centralizer_iff.mp hxcent) w (s.S_le_R hw)
    have hqw : q⁻¹ * w = w * q⁻¹ :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hqC)) w (s3_S_le_L s hw)).symm
    exact comm_of_eq_mul_inv hy_eq hxw hqw
  have hyZ : y ∈ s.fr.Z := by
    have h := hycen
    rwa [s3_cen_S s hA] at h
  rw [SFrame.Z] at hyZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyZ
  exact ⟨k, q, hqQ, by rw [hxyq, hk]⟩

theorem s3_zt_le_cen_T (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) :
    zt s ≤ cen s.T := by
  have hA : LFactsA s := lfactsA_of_setting hS hZ s
  have hzS : s.fr.z ∈ s.fr.S := s3_A_le_S s (s3_z_mem_A s)
  have hzT : s.fr.z ∈ s.T := s3_z_mem_T s
  have htcen : s.t ∈ cen s.T := by
    refine Subgroup.mem_inf.mpr ⟨s3_t_mem_T s, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact s3_comm_t_of_mem_T s hg
  have hzcen : s.fr.z ∈ cen s.T := by
    refine Subgroup.mem_inf.mpr ⟨hzT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hN := s3_S_normal_T s hS
    have hconjS : g * s.fr.z * g⁻¹ ∈ s.fr.S := by
      have h := hN.conj_mem ⟨s.fr.z, hzT⟩ (Subgroup.mem_subgroupOf.mpr hzS) ⟨g, hg⟩
      exact Subgroup.mem_subgroupOf.mp h
    have hconj_invS : ∀ u ∈ s.fr.S, g⁻¹ * u * g ∈ s.fr.S := by
      intro u hu
      have h := hN.conj_mem ⟨u, s3_S_le_T s hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
        ⟨g⁻¹, Subgroup.inv_mem _ hg⟩
      simpa using Subgroup.mem_subgroupOf.mp h
    have hzcenS : s.fr.z ∈ cen s.fr.S := (s3_cen_S s hA).symm ▸ Subgroup.mem_zpowers s.fr.z
    have hzcent : s.fr.z ∈ centralizer (s.fr.S : Set G) := (Subgroup.mem_inf.mp hzcenS).2
    have hconjcen : g * s.fr.z * g⁻¹ ∈ centralizer (s.fr.S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hzu : (g⁻¹ * u * g) * s.fr.z = s.fr.z * (g⁻¹ * u * g) :=
        (Subgroup.mem_centralizer_iff.mp hzcent) (g⁻¹ * u * g) (hconj_invS u hu)
      calc u * (g * s.fr.z * g⁻¹)
          = g * ((g⁻¹ * u * g) * s.fr.z) * g⁻¹ := by group
        _ = g * (s.fr.z * (g⁻¹ * u * g)) * g⁻¹ := by rw [hzu]
        _ = (g * s.fr.z * g⁻¹) * u := by group
    have hmem : g * s.fr.z * g⁻¹ ∈ s.fr.Z := by
      have h : g * s.fr.z * g⁻¹ ∈ cen s.fr.S := Subgroup.mem_inf.mpr ⟨hconjS, hconjcen⟩
      rwa [s3_cen_S s hA] at h
    rw [SFrame.Z] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hkmod : s.fr.z ^ k = 1 ∨ s.fr.z ^ k = s.fr.z := by
      have h := zpow_mod_orderOf s.fr.z k
      rw [s3_z_order s hA] at h
      rcases Int.emod_two_eq_zero_or_one k with h2 | h2
      · left
        rw [← h, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h2]
        simp
      · right
        rw [← h, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h2]
        simp
    rcases hkmod with h1 | hz
    · exfalso
      have hz1 : s.fr.z = 1 := by
        calc s.fr.z = g⁻¹ * (g * s.fr.z * g⁻¹) * g := by group
          _ = 1 := by rw [← hk, h1]; group
      have hord := s3_z_order s hA
      rw [hz1, orderOf_one] at hord
      norm_num at hord
    · calc g * s.fr.z = (g * s.fr.z * g⁻¹) * g := by group
        _ = s.fr.z * g := by rw [← hk, hz]
  rw [zt, Subgroup.closure_le]
  intro w hw
  rcases (by simpa using hw : w = s.fr.z ∨ w = s.t) with rfl | rfl
  · exact hzcen
  · exact htcen

theorem s3_cen_R_eq (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t) : cen s.R = zt s := by
  have hztR : zt s ≤ s.R := by
    rw [zt, Subgroup.closure_le]
    intro w hw
    rcases (by simpa using hw : w = s.fr.z ∨ w = s.t) with rfl | rfl
    · exact s.S_le_R (s3_A_le_S s (s3_z_mem_A s))
    · exact s3_t_mem_R s
  refine le_antisymm (fun x hx => ?_) (fun w hw => ?_)
  · obtain ⟨k, q, hqQ, hxeq⟩ := s3_cen_R_le s hS hZ x hx
    rw [hxeq]
    rw [hQ] at hqQ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hqQ
    rw [← hn]
    exact Subgroup.mul_mem _
      (Subgroup.zpow_mem (zt s) (Subgroup.subset_closure (by simp)) k)
      (Subgroup.zpow_mem (zt s) (Subgroup.subset_closure (by simp)) n)
  · refine Subgroup.mem_inf.mpr ⟨hztR hw, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (s3_zt_le_cen_T s hS hZ hw)).2) r (s.R_le_T hr)

theorem s3_cen_T_eq (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2)
    (hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t) : cen s.T = zt s := by
  refine le_antisymm (fun x hx => ?_) (s3_zt_le_cen_T s hS hZ)
  obtain ⟨k, q, hqQ, hxeq⟩ := s3_cen_T_le s hS hZ hOut x hx
  rw [hxeq]
  rw [hQ] at hqQ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hqQ
  rw [← hn]
  exact Subgroup.mul_mem _
    (Subgroup.zpow_mem (zt s) (Subgroup.subset_closure (by simp)) k)
    (Subgroup.zpow_mem (zt s) (Subgroup.subset_closure (by simp)) n)

end CFSG.OddStandard.HigherRank.YamadaG23
