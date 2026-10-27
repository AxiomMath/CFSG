module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Cyc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31CenT

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_NT_fix_t_RT (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hRT : s.R = s.T) (hQ : ∃ q ∈ s.T ⊓ centralizer (L : Set G), q ∉ zpowers s.t) :
    ∀ n ∈ normalizer (s.T : Set G), n * s.t * n⁻¹ = s.t := by
  haveI : IsCyclic ↥(s.T ⊓ centralizer (L : Set G)) := s3_Q_cyclic s hS
  obtain ⟨q₀, hq₀, hq₀t⟩ := hQ
  obtain ⟨q, hq, hq2⟩ := s3_Q_sq_root s hS hq₀ hq₀t
  have hqT : q ∈ s.T := (Subgroup.mem_inf.mp hq).1
  have hqC : q ∈ centralizer (L : Set G) := (Subgroup.mem_inf.mp hq).2
  have hqcen : q ∈ cen s.T := by
    refine Subgroup.mem_inf.mpr ⟨hqT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨x, hxS, q', hq', rfl⟩ := s3_R_eq_SQ s hS hZ r (hRT.symm ▸ hr)
    have hqx : x * q = q * x :=
      Subgroup.mem_centralizer_iff.mp hqC x (s3_S_le_L s hxS)
    have hqq' : q * q' = q' * q :=
      congrArg Subtype.val
        (mul_comm' (⟨q, hq⟩ : ↥(s.T ⊓ centralizer (L : Set G))) ⟨q', hq'⟩)
    calc (x * q') * q = x * (q' * q) := by group
      _ = x * (q * q') := by rw [hqq']
      _ = (x * q) * q' := by group
      _ = (q * x) * q' := by rw [hqx]
      _ = q * (x * q') := by group
  have hconj_cen : ∀ n ∈ normalizer (s.T : Set G), n * q * n⁻¹ ∈ cen s.T := by
    intro n hn
    have hn' := Subgroup.mem_normalizer_iff.mp hn
    refine Subgroup.mem_inf.mpr ⟨(hn' q).mp hqT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ s.T := by
      refine (hn' (n⁻¹ * y * n)).mpr ?_
      have heq : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      rwa [heq]
    have hcomm := (Subgroup.mem_inf.mp hqcen).2 (n⁻¹ * y * n) hy'
    calc y * (n * q * n⁻¹) = n * ((n⁻¹ * y * n) * q) * n⁻¹ := by group
      _ = n * (q * (n⁻¹ * y * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * q * n⁻¹) * y := by group
  intro n hn
  have hxcenR : n * q * n⁻¹ ∈ cen s.R := by rw [hRT]; exact hconj_cen n hn
  obtain ⟨k, q'', hq'', hconj⟩ := s3_cen_R_le s hS hZ (n * q * n⁻¹) hxcenR
  have hzz : s.fr.z * s.fr.z = 1 := by
    rw [← pow_two, ← (lfactsA_of_setting hS hZ s).z_order]
    exact pow_orderOf_eq_one s.fr.z
  have hz2 : s.fr.z ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two, hzz]
  have hzk2 : (s.fr.z ^ k) ^ 2 = 1 := by
    rw [show (s.fr.z ^ k) ^ 2 = (s.fr.z ^ k) ^ ((2 : ℕ) : ℤ) from
        (zpow_natCast _ 2).symm,
      ← zpow_mul, zpow_mul', hz2, one_zpow]
  have hzkq : Commute (s.fr.z ^ k) q'' :=
    (show Commute s.fr.z q'' from
      Subgroup.mem_centralizer_iff.mp hq''.2 s.fr.z (s3_z_mem_L s)).zpow_left k
  have hsq : (s.fr.z ^ k * q'') ^ 2 = q'' ^ 2 := by
    rw [hzkq.mul_pow 2, hzk2, one_mul]
  have hnt : (n * q * n⁻¹) ^ 2 = n * s.t * n⁻¹ := by
    rw [show n * q * n⁻¹ = (MulAut.conj n) q by rw [MulAut.conj_apply],
      ← map_pow (MulAut.conj n) q 2, hq2, MulAut.conj_apply]
  have hnt2 : n * s.t * n⁻¹ = q'' ^ 2 := by rw [← hnt, hconj, hsq]
  have hmem : q'' ^ 2 ∈ s.T ⊓ centralizer (L : Set G) := Subgroup.pow_mem _ hq'' 2
  have horder : orderOf (q'' ^ 2) = 2 := by
    have hsc : SemiconjBy n s.t (n * s.t * n⁻¹) := by
      show n * s.t = (n * s.t * n⁻¹) * n
      group
    rw [← hnt2, ← SemiconjBy.orderOf_eq n hsc, s.t_order]
  exact hnt2.trans (s3_Q_invol s hS hmem horder)

end CFSG.OddStandard.HigherRank.YamadaG23
