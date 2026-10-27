module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31CenT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31FrSq

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_no_fourth_root (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2)
    (hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t) : ∀ v : G, v ^ 4 ≠ s.t := by
  intro v hv
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting (L := L) hS
  have ht2 : s.t ^ 2 = 1 := by rw [← s.t_order]; exact pow_orderOf_eq_one s.t
  have hvt : v * s.t = s.t * v := by rw [← hv]; group
  have hvH : v ∈ s.H := by
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
    exact hvt
  have hdvd : orderOf v ∣ 2 ^ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [show (2 : ℕ) ^ 3 = 4 * 2 by norm_num, pow_mul, hv, ht2]
  have hpg : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 3) (by rw [Nat.card_zpowers]; exact hdvd)
  obtain ⟨h, hhH, hconj⟩ := exists_conj_le_isSylowIn (V := s.H) (P := s.T)
    (Q := Subgroup.zpowers v) s.sylow_T hpg (Subgroup.zpowers_le.mpr hvH)
  have hhcomm : h * s.t = s.t * h := by
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff] at hhH
    exact hhH
  let w : G := h * v * h⁻¹
  have hwT : w ∈ s.T := by
    have hwmem : (MulAut.conj h) v ∈ conjSub h (Subgroup.zpowers v) := by
      rw [conjSub]
      exact Subgroup.mem_map.mpr ⟨v, Subgroup.mem_zpowers v, rfl⟩
    simpa [w, MulAut.conj_apply] using hconj hwmem
  have hw4 : w ^ 4 = s.t := by
    have hconj_ht : h * s.t * h⁻¹ = s.t := by rw [hhcomm]; group
    calc w ^ 4 = h * v ^ 4 * h⁻¹ := by simp [w]
      _ = h * s.t * h⁻¹ := by rw [hv]
      _ = s.t := hconj_ht
  let α : MulAut (L ⧸ center L) := jOn L (s3_T_le_N s hS) ⟨w, hwT⟩
  have hαacts : ActsAs L w α := jOn_actsAs L (s3_T_le_N s hS) ⟨w, hwT⟩
  have hαmem : α ∈ jSub L s.T := by
    rw [← range_jOn L (s3_T_le_N s hS)]
    exact MonoidHom.mem_range.mpr ⟨⟨w, hwT⟩, rfl⟩
  have hα2S : α ^ 2 ∈ s.fr'.S := by
    by_cases hRT : s.R = s.T
    · have hmem : α ∈ jSub L s.R := by rw [hRT]; exact hαmem
      rw [s3_jSub_R s] at hmem
      exact Subgroup.pow_mem s.fr'.S hmem 2
    · have hmem : α ∈ s.fr'.Sσ := by
        rw [← s3_jSub_T s hS hOut hRT]
        exact hαmem
      exact frame_sq_mem_S s.fr' s.facts.1 hmem
  have hα2j : α ^ 2 ∈ jSub L s.fr.S := by rwa [s3_jSub_S s]
  obtain ⟨x, hxS, hxacts⟩ := (mem_jSub L).mp hα2j
  have hw2acts : ActsAs L (w ^ 2) (α ^ 2) := by
    have := actsAs_mul L hαacts hαacts
    simpa [pow_two] using this
  have hxdacts : ActsAs L (x⁻¹ * w ^ 2) (1 : MulAut (L ⧸ center L)) := by
    have h1 : ActsAs L x⁻¹ (α ^ 2)⁻¹ := actsAs_inv L hxacts
    have h2 := actsAs_mul L h1 hw2acts
    simpa using h2
  have hxC : x⁻¹ * w ^ 2 ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hxdacts
  have hxT : x⁻¹ * w ^ 2 ∈ s.T :=
    Subgroup.mul_mem s.T (Subgroup.inv_mem s.T (s3_S_le_T s hxS)) (Subgroup.pow_mem s.T hwT 2)
  have hxQ : x⁻¹ * w ^ 2 ∈ zpowers s.t := by
    rw [← hQ]
    exact Subgroup.mem_inf.mpr ⟨hxT, hxC⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxQ
  have hw2 : w ^ 2 = x * s.t ^ k := by rw [hk]; group
  have htk_comm : s.t ^ k * x = x * s.t ^ k := by
    have htx : s.t ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (s3_comm_t_of_mem_L s (s3_S_le_L s hxS)).symm
    have hmem := Subgroup.zpow_mem (Subgroup.centralizer ({x} : Set G)) htx k
    rwa [Subgroup.mem_centralizer_singleton_iff] at hmem
  have htk2 : s.t ^ k * s.t ^ k = 1 := by
    rw [← zpow_add, show k + k = 2 * k by ring, zpow_mul]
    have h2 : s.t ^ (2 : ℤ) = 1 := by simpa using ht2
    rw [h2, one_zpow]
  have hw4x : w ^ 4 = x ^ 2 := by
    calc w ^ 4 = (w ^ 2) ^ 2 := by group
      _ = (x * s.t ^ k) ^ 2 := by rw [hw2]
      _ = x ^ 2 := by
        rw [pow_two, pow_two]
        calc (x * s.t ^ k) * (x * s.t ^ k)
            = x * (s.t ^ k * x) * s.t ^ k := by group
          _ = x * (x * s.t ^ k) * s.t ^ k := by rw [htk_comm]
          _ = (x * x) * (s.t ^ k * s.t ^ k) := by group
          _ = x * x := by rw [htk2, mul_one]
  have htS : s.t ∈ s.fr.S := by
    rw [show s.t = x ^ 2 by rw [← hw4, hw4x]]
    exact Subgroup.pow_mem s.fr.S hxS 2
  have ht1 : s.t = 1 := s3_S_inf_cent s hS hZ s.t htS s.t_mem
  have h21 : (2 : ℕ) = 1 := by rw [← s.t_order, ht1, orderOf_one]
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
