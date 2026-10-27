module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31CenT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Fus1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31NT

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem mem_cen_conj {H : Type} [Group H] {T : Subgroup H} {n : H}
    (hn : n ∈ Subgroup.normalizer (T : Set H)) {x : H} (hx : x ∈ cen T) :
    n * x * n⁻¹ ∈ cen T := by
  rw [Subgroup.mem_normalizer_iff] at hn
  simp only [cen, Subgroup.mem_inf] at hx ⊢
  refine ⟨(hn x).mp hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have hy' : n⁻¹ * y * n ∈ T :=
    (hn (n⁻¹ * y * n)).mpr (by rw [show n * (n⁻¹ * y * n) * n⁻¹ = y by group]; exact hy)
  have hc := hx.2 (n⁻¹ * y * n) hy'
  calc y * (n * x * n⁻¹)
      = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
    _ = (n * x * n⁻¹) * y := by group

private theorem normalizer_le_normalizer_cen {H : Type} [Group H] (T : Subgroup H) :
    Subgroup.normalizer (T : Set H) ≤ Subgroup.normalizer (cen T : Set H) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact mem_cen_conj hn
  · intro hx
    have hninv : n⁻¹ ∈ Subgroup.normalizer (T : Set H) := Subgroup.inv_mem _ hn
    have h := mem_cen_conj hninv hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ = x by group] at h

theorem s3_conjClass_eq (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2)
    (hQ : s.T ⊓ centralizer (L : Set G) = zpowers s.t) (hc : ∀ g : G, g * s.t * g⁻¹ ∉ L) :
    conjClass (normalizer (cen s.R : Set G)) s.t = s.tCoset (cen s.fr.S) := by
  have hA : LFactsA s := lfactsA_of_setting hS hZ s
  have hcenR : cen s.R = zt s := s3_cen_R_eq s hS hZ hQ
  have hcenT : cen s.T = zt s := s3_cen_T_eq s hS hZ hOut hQ
  ext w
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [hcenR] at hn
    have hmem : n * s.t * n⁻¹ ∈ zt s :=
      (Subgroup.mem_normalizer_iff.mp hn s.t).mp (Subgroup.subset_closure (by simp))
    rcases (s3_mem_zt_iff s hA).mp hmem with h1 | hz | ht | hzt
    · exfalso
      have ht1 : s.t = 1 := by
        have h : s.t * n⁻¹ = n⁻¹ := by
          calc s.t * n⁻¹ = n⁻¹ * (n * s.t * n⁻¹) := by group
            _ = n⁻¹ * 1 := by rw [h1]
            _ = n⁻¹ := mul_one _
        calc s.t = (s.t * n⁻¹) * n := by group
          _ = n⁻¹ * n := by rw [h]
          _ = 1 := by group
      exact absurd s.t_order (by rw [ht1, orderOf_one]; norm_num)
    · exfalso
      exact (hc n) (hz.symm ▸ s3_z_mem_L s)
    · exact ⟨1, Subgroup.one_mem _, by rw [ht, one_mul]⟩
    · refine ⟨s.fr.z, ?_, by rw [hzt]⟩
      rw [s3_cen_S s hA, SFrame.Z]
      exact Subgroup.mem_zpowers s.fr.z
  · rintro ⟨y, hy, rfl⟩
    rw [s3_cen_S s hA, SFrame.Z] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hmod := zpow_mod_orderOf s.fr.z k
    rw [s3_z_order s hA] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · have hk : s.fr.z ^ k = 1 := by
        rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
        simp
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hk, one_mul]
      simp
    · have hk : s.fr.z ^ k = s.fr.z := by
        rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
        simp
      rw [hk]
      obtain ⟨g, hgz | hgzt⟩ := s3_fusion_zt s hS hZ hOut
      · exfalso
        exact (hc g) (hgz.symm ▸ s3_z_mem_L s)
      · have hgu : g * s.t * g⁻¹ ∈ cen s.T := by
          rw [hcenT]
          exact (s3_mem_zt_iff s hA).mpr (Or.inr (Or.inr (Or.inr hgzt)))
        obtain ⟨n, hnT, hn⟩ := s3_fusion_NT s hgu
        have hninvT : n⁻¹ ∈ Subgroup.normalizer (s.T : Set G) := Subgroup.inv_mem _ hnT
        have hninv_cen : n⁻¹ ∈ Subgroup.normalizer (cen s.T : Set G) :=
          normalizer_le_normalizer_cen s.T hninvT
        have hninvN : n⁻¹ ∈ Subgroup.normalizer (cen s.R : Set G) := by
          rw [hcenR.trans hcenT.symm]
          exact hninv_cen
        refine ⟨n⁻¹, hninvN, ?_⟩
        have h2 : n⁻¹ * (n * (g * s.t * g⁻¹) * n⁻¹) * n = g * s.t * g⁻¹ := by group
        have h1 : n⁻¹ * (n * (g * s.t * g⁻¹) * n⁻¹) * n = n⁻¹ * s.t * n := by rw [hn]
        rw [inv_inv, ← hgzt]
        exact h2.symm.trans h1

end CFSG.OddStandard.HigherRank.YamadaG23
