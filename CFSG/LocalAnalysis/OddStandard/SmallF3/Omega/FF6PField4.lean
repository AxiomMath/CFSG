module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSyl1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PNoZ4b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6p_cent_B_sylow (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ H S₁ : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) → IsSylow2Of S₁ H →
      ∀ B : Subgroup G, IsNormalE16In (S₁ ⊓ L) B →
        ∀ x ∈ H, (∀ b ∈ B, x * b = b * x) → ∃ s ∈ S₁, s⁻¹ * x ∈ centralizer (L : Set G) := by
  intro G _ _ L h H S₁ hLH hHN hS B hB x hxH hxB
  have hP : IsSylow2Of (S₁ ⊓ L) L :=
    sec8t84_sylow_inf_normal hS hLH fun h hh n hn =>
      (Subgroup.mem_normalizer_iff.mp (hHN hh) n).mp hn
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ, hBφ⟩ :=
    ff6p_exists_model_PB h hP hB
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc h
  have hBL : B ≤ L := hB.1.trans inf_le_right
  have hzB : ∀ w ∈ ffB1p hQ fr,
      ffTheta6P hQ hdim hsgn e ⟨x, hHN hxH⟩ * ffOmegaToSim hQ w =
        ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨x, hHN hxH⟩ := by
    have h := (ff6p_commute_img_iff hQ hdim hsgn hz e (hHN hxH) hBL).mp hxB
    rwa [hBφ] at h
  rcases ff6p_cent_sim_cases hQ h2 fr hzB with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · have hb' : b ∈ ffImg (ff6mPhi e) B := by rwa [hBφ]
    obtain ⟨b₀, hb₀B, hb₀φ⟩ := mem_ffImg_iff.mp hb'
    refine ⟨(b₀ : G), (Subgroup.mem_inf.mp (hB.1 hb₀B)).1, ?_⟩
    have hbmN : (b₀ : G)⁻¹ * x ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem ((Subgroup.normalizer (L : Set G)).inv_mem
        (Subgroup.le_normalizer b₀.2)) (hHN hxH)
    have hm : (⟨(b₀ : G)⁻¹ * x, hbmN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨(b₀ : G), Subgroup.le_normalizer b₀.2⟩ :
          ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨x, hHN hxH⟩ := Subtype.ext rfl
    have hθ : ffTheta6P hQ hdim hsgn e ⟨(b₀ : G)⁻¹ * x, hbmN⟩ = 1 := by
      rw [hm, map_mul, map_inv, ffTheta6P_of_mem, hb₀φ]
      rw [hzb, inv_mul_cancel]
    exact (ff6p_theta_eq_one_iff h hQ hdim hsgn e hbmN).mp hθ
  · have hb1 : b ∈ ffB1p hQ fr := hb
    have hb' : b ∈ ffImg (ff6mPhi e) B := by rwa [hBφ]
    obtain ⟨b₀, hb₀B, hb₀φ⟩ := mem_ffImg_iff.mp hb'
    have hπ : piOrth Q ∉ omegaGroup hQ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
    have hc : ffTs fr * ffOmegaToSim hQ b = ffOmegaToSim hQ b * ffTs fr :=
      ffTs_comm_normalizer hQ h2 hπ fr (Subgroup.le_normalizer hb1)
    have hbmN : (b₀ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer b₀.2
    have hx'N : (b₀ : G)⁻¹ * x ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem ((Subgroup.normalizer (L : Set G)).inv_mem hbmN) (hHN hxH)
    have hx'H : (b₀ : G)⁻¹ * x ∈ H := H.mul_mem (H.inv_mem (hLH b₀.2)) hxH
    have hm : (⟨(b₀ : G)⁻¹ * x, hx'N⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨(b₀ : G), hbmN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
          ⟨x, hHN hxH⟩ := Subtype.ext rfl
    have hθx' : ffTheta6P hQ hdim hsgn e ⟨(b₀ : G)⁻¹ * x, hx'N⟩ = ffTs fr := by
      rw [hm, map_mul, map_inv, ffTheta6P_of_mem, hb₀φ]
      rw [hzb, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    have htsH : ffTs fr ∈ ffThetaImg (ffTheta6P hQ hdim hsgn e) H :=
      mem_ffThetaImg_iff.mpr ⟨(b₀ : G)⁻¹ * x, hx'N, hx'H, hθx'⟩
    obtain ⟨s', hs'N, hs'S1, hθs'⟩ := mem_ffThetaImg_iff.mp
      (ff6p_ts_mem_thetaImg hQ hdim hsgn e fr hHN hS hPφ htsH)
    refine ⟨(b₀ : G) * s', S₁.mul_mem (Subgroup.mem_inf.mp (hB.1 hb₀B)).1 hs'S1, ?_⟩
    have hgH : ((b₀ : G) * s')⁻¹ * x ∈ H :=
      H.mul_mem (H.inv_mem (H.mul_mem (hLH b₀.2) (hS.1 hs'S1))) hxH
    have hgN : ((b₀ : G) * s')⁻¹ * x ∈ Subgroup.normalizer (L : Set G) := hHN hgH
    have hθ : ffTheta6P hQ hdim hsgn e ⟨((b₀ : G) * s')⁻¹ * x, hgN⟩ = 1 := by
      have hm2 : (⟨((b₀ : G) * s')⁻¹ * x, hgN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ((⟨(b₀ : G), hbmN⟩ : ↥(Subgroup.normalizer (L : Set G))) *
            ⟨s', hs'N⟩)⁻¹ * ⟨x, hHN hxH⟩ := Subtype.ext rfl
      rw [hm2, map_mul, map_inv, map_mul, ffTheta6P_of_mem, hb₀φ]
      rw [hθs', hzb, ← hc, inv_mul_cancel]
    exact (ff6p_theta_eq_one_iff h hQ hdim hsgn e hgN).mp hθ

theorem ff6p_no_normal_z4 (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ H S₁ : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) → IsSylow2Of S₁ H →
      ∀ w ∈ S₁, w ^ 4 ∈ centralizer (L : Set G) → w ^ 2 ∉ centralizer (L : Set G) →
        (∀ y ∈ S₁, y⁻¹ * w * y ∈ zpowers w ⊔ centralizer (L : Set G)) → False := by
  intro G _ _ L h H S₁ hLH hHN hS w hwS1 hw4 hw2 hnorm
  have hP : IsSylow2Of (S₁ ⊓ L) L :=
    sec8t84_sylow_inf_normal hS hLH fun h hh n hn =>
      (Subgroup.mem_normalizer_iff.mp (hHN hh) n).mp hn
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ⟩ := ff6p_exists_model_P h hP
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := hHN (hS.1 hwS1)
  set z : ProjSim Q := ffTheta6P hQ hdim hsgn e ⟨w, hwN⟩ with hz_def
  have hz4 : z ^ 4 = 1 := by
    rw [hz_def, ← map_pow]
    rw [show (⟨w, hwN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 4 =
      ⟨w ^ 4, (Subgroup.normalizer (L : Set G)).pow_mem hwN 4⟩ from Subtype.ext rfl]
    exact (ff6p_theta_eq_one_iff h hQ hdim hsgn e _).mpr hw4
  have hz2 : z ^ 2 ≠ 1 := by
    intro h1
    apply hw2
    rw [hz_def, ← map_pow] at h1
    rw [show (⟨w, hwN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 =
      ⟨w ^ 2, (Subgroup.normalizer (L : Set G)).pow_mem hwN 2⟩ from Subtype.ext rfl] at h1
    exact (ff6p_theta_eq_one_iff h hQ hdim hsgn e _).mp h1
  let U : Subgroup ↥(Subgroup.normalizer (L : Set G)) :=
    (Subgroup.zpowers z).comap (ffTheta6P hQ hdim hsgn e)
  let Ũ : Subgroup G := U.map (Subgroup.normalizer (L : Set G)).subtype
  have hw_mem : w ∈ Ũ := by
    refine Subgroup.mem_map.mpr ⟨⟨w, hwN⟩, ?_, rfl⟩
    change ffTheta6P hQ hdim hsgn e ⟨w, hwN⟩ ∈ Subgroup.zpowers z
    rw [← hz_def]
    exact Subgroup.mem_zpowers z
  have hcent_mem : Subgroup.centralizer (L : Set G) ≤ Ũ := by
    intro c hc
    have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.centralizer_le_normalizer (L : Set G) hc
    refine Subgroup.mem_map.mpr ⟨⟨c, hcN⟩, ?_, rfl⟩
    change ffTheta6P hQ hdim hsgn e ⟨c, hcN⟩ ∈ Subgroup.zpowers z
    rw [(ff6p_theta_eq_one_iff h hQ hdim hsgn e hcN).mpr hc]
    exact Subgroup.one_mem _
  have hnorm_le : Subgroup.zpowers w ⊔ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hwN) (Subgroup.centralizer_le_normalizer (L : Set G))
  have hZ_le : Subgroup.zpowers w ⊔ Subgroup.centralizer (L : Set G) ≤ Ũ :=
    sup_le (Subgroup.zpowers_le.mpr hw_mem) hcent_mem
  have key : ∀ (g : G) (hg : g ∈ Subgroup.zpowers w ⊔ Subgroup.centralizer (L : Set G))
      (hgN : g ∈ Subgroup.normalizer (L : Set G)),
      ffTheta6P hQ hdim hsgn e ⟨g, hgN⟩ ∈ Subgroup.zpowers z := by
    intro g hg hgN
    obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp (hZ_le hg)
    have heq : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (L : Set G))) = n := Subtype.ext hne.symm
    rw [heq]
    exact Subgroup.mem_comap.mp hn
  have hnorm' : ∀ p ∈ ffP1p hQ fr,
      ffOmegaToSim hQ p * z * (ffOmegaToSim hQ p)⁻¹ ∈ Subgroup.zpowers z := by
    intro p hp
    have hp' : p ∈ ffImg (ff6mPhi e) (S₁ ⊓ L) := by rwa [hPφ]
    obtain ⟨m, hm, hmφ⟩ := mem_ffImg_iff.mp hp'
    obtain ⟨hmS1, hmL⟩ := Subgroup.mem_inf.mp hm
    have hmN : (m : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hmL
    have hgZ : (m : G) * w * (m : G)⁻¹ ∈
        Subgroup.zpowers w ⊔ Subgroup.centralizer (L : Set G) := by
      simpa using hnorm (m : G)⁻¹ (S₁.inv_mem hmS1)
    have hgN : (m : G) * w * (m : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := hnorm_le hgZ
    have hθm : ffTheta6P hQ hdim hsgn e ⟨(m : G), hmN⟩ = ffOmegaToSim hQ p := by
      rw [ffTheta6P_of_mem, hmφ]
    have hθg : ffTheta6P hQ hdim hsgn e ⟨(m : G) * w * (m : G)⁻¹, hgN⟩ =
        ffOmegaToSim hQ p * z * (ffOmegaToSim hQ p)⁻¹ := by
      have hm2 : (⟨(m : G) * w * (m : G)⁻¹, hgN⟩ :
            ↥(Subgroup.normalizer (L : Set G))) =
          ⟨(m : G), hmN⟩ * ⟨w, hwN⟩ * (⟨(m : G), hmN⟩)⁻¹ := Subtype.ext rfl
      rw [hm2, map_mul, map_mul, map_inv, hθm, ← hz_def]
    rw [← hθg]
    exact key ((m : G) * w * (m : G)⁻¹) hgZ hgN
  exact ff6p_no_cyclic4 hQ hdim hsgn h2 fr hz4 hz2 hnorm'

end CFSG.OddStandard.SmallF3.Omega
