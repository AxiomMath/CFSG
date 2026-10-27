module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Cyc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31CenT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Z2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

private lemma conj_mem_cen {G : Type} [Group G] {T : Subgroup G} {n : G}
    (hn : n ∈ normalizer (T : Set G)) {c : G}
    (hc : c ∈ T ⊓ centralizer (T : Set G)) :
    n * c * n⁻¹ ∈ T ⊓ centralizer (T : Set G) := by
  rw [Subgroup.mem_inf] at hc ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn c).mp hc.1, ?_⟩
  have hfix : (MulAut.conj n).toMonoidHom '' (T : Set G) = T := by
    simpa only [MulEquiv.coe_toMonoidHom] using Subgroup.mem_normalizer_iff_conj_image_eq.mp hn
  have hmap :=
    Subgroup.map_centralizer_le_centralizer_image (T : Set G) (MulAut.conj n).toMonoidHom
  rw [hfix] at hmap
  have hmem : (MulAut.conj n) c ∈ centralizer (T : Set G) :=
    hmap (Subgroup.mem_map.mpr ⟨c, hc.2, rfl⟩)
  simpa only [MulAut.conj_apply] using hmem

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_NT_fix_t_RneT (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (hRT : s.R ≠ s.T)
    (hQ : ∃ q ∈ s.T ⊓ centralizer (L : Set G), q ∉ zpowers s.t) :
    ∀ n ∈ normalizer (s.T : Set G), n * s.t * n⁻¹ = s.t := by
  obtain ⟨q₀, hq₀, hq₀t⟩ := hQ
  obtain ⟨q, hq, hq2⟩ := s3_Q_sq_root s hS hq₀ hq₀t
  have ht_cen : s.t ∈ cen s.T :=
    s3_zt_le_cen_T s hS hZ (Subgroup.subset_closure (by simp))
  have hqT : q ∈ s.T := (Subgroup.mem_inf.mp hq).1
  have hcomm_q : ∀ y ∈ s.T, q * y * q⁻¹ * y⁻¹ ∈ cen s.T := by
    intro y hy
    have hyq : y * q * y⁻¹ ∈ s.T ⊓ centralizer (L : Set G) := s3_Q_normalized s hS hy hq
    have hyq2 : (y * q * y⁻¹) ^ 2 = s.t := by
      have hpow : (y * q * y⁻¹) ^ 2 = y * q ^ 2 * y⁻¹ := by
        have h := map_pow (MulAut.conj y) q 2
        simp only [MulAut.conj_apply] at h
        exact h.symm
      have hyt : y * s.t * y⁻¹ = s.t := by
        have hcomm : y * s.t = s.t * y :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ht_cen).2) y hy
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hpow, hq2, hyt]
    have haz : q * y * q⁻¹ * y⁻¹ = q * (y * q * y⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_inv_cancel,
        mul_one, one_mul]
    rcases s3_Q_sq_unique s hS hq hyq hq2 hyq2 with h | h
    · rw [haz, h, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [haz, h, inv_inv, ← pow_two, hq2]
      exact ht_cen
  intro n hn
  have hn' := Subgroup.mem_normalizer_iff.mp hn
  have hxT : n * q * n⁻¹ ∈ s.T := (hn' q).mp hqT
  have hx2 : ∀ y ∈ s.T, (n * q * n⁻¹) * y * (n * q * n⁻¹)⁻¹ * y⁻¹ ∈ cen s.T := by
    intro y hy
    have hy' : n⁻¹ * y * n ∈ s.T := by
      refine (hn' (n⁻¹ * y * n)).mpr ?_
      have heq : n * (n⁻¹ * y * n) * n⁻¹ = y := by
        simp only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul,
          inv_mul_cancel_left, mul_inv_cancel_left]
      rwa [heq]
    have hconj := conj_mem_cen hn (hcomm_q (n⁻¹ * y * n) hy')
    have heq : (n * q * n⁻¹) * y * (n * q * n⁻¹)⁻¹ * y⁻¹
        = n * (q * (n⁻¹ * y * n) * q⁻¹ * (n⁻¹ * y * n)⁻¹) * n⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_inv_cancel,
        mul_one, one_mul]
    rw [heq]; exact hconj
  have hsqQ := s3_sq_mem_Q_of_Z2 s hS hOut hRT hxT hx2
  have hsq : (n * q * n⁻¹) ^ 2 = n * s.t * n⁻¹ := by
    have h := map_pow (MulAut.conj n) q 2
    simp only [MulAut.conj_apply] at h
    rw [← h, hq2]
  have hmem : n * s.t * n⁻¹ ∈ s.T ⊓ centralizer (L : Set G) := hsq ▸ hsqQ
  have horder : orderOf (n * s.t * n⁻¹) = 2 := by
    have hsc : SemiconjBy n s.t (n * s.t * n⁻¹) := by
      show n * s.t = (n * s.t * n⁻¹) * n
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [← SemiconjBy.orderOf_eq n hsc, s.t_order]
  exact s3_Q_invol s hS hmem horder

end CFSG.OddStandard.HigherRank.YamadaG23
