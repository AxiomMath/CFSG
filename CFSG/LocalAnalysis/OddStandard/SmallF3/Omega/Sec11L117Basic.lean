module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS3

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_t_mem_S [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) : t ∈ S :=
  (hp.basic G t L S z hctx.toSec10Z).2.2.2.1

theorem sec11_invols [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) :
    t * t = 1 ∧ z * z = 1 ∧ t * z = z * t ∧ t ≠ 1 ∧ z ≠ 1 := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution, pow_two] at h
    exact h
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hctx.toSec10Z.pocket.1, pow_two] at h
    exact h
  have htz : t * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hctx.mem_S)).symm
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := hctx.involution
    rw [h, orderOf_one] at h2
    omega
  have hz1 : z ≠ 1 := by
    intro h
    have h2 := hctx.toSec10Z.pocket.1
    rw [h, orderOf_one] at h2
    omega
  exact ⟨ht2, hz2, htz, ht1, hz1⟩

theorem sec11_Q_facts [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    z ∈ secQ K1 K2 ∧ secQ K1 K2 ≤ S ∧ secQ K1 K2 ≤ L ∧ (∀ q ∈ secQ K1 K2, q * z = z * q) ∧
      ∀ q ∈ secQ K1 K2, t * q = q * t := by
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  have hQSL := sec10J_Q_le hp.facts.pockets5 hp.basic hctx
  have hzQ := (sec10KS_Q_elem hp.facts.pockets5 hp.facts.centZ5 hpsp hctx).1
  have htC : t ∈ centralizer (L : Set G) := (hp.basic G t L S z hctx.toSec10Z).2.1
  refine ⟨hzQ, hQSL.trans inf_le_left, hQSL.trans inf_le_right, fun q hq => ?_, fun q hq => ?_⟩
  · exact hctx.central q (hQSL hq).1
  · exact (Subgroup.mem_centralizer_iff.mp htC q (hQSL hq).2).symm

theorem sec11_t_mem_D [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : t ∈ secD K1 K2 R := by
  obtain ⟨-, -, -, -, hQt⟩ := sec11_Q_facts hp hctx.toSec10Ctx
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun q hq => ?_,
    hctx.T_le (hctx.S_le (sec11_t_mem_S hp hctx.toSec10Ctx))⟩
  exact (hQt q hq).symm

theorem sec11_z_mem_D [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : z ∈ secD K1 K2 R := by
  obtain ⟨-, -, -, hQz, -⟩ := sec11_Q_facts hp hctx.toSec10Ctx
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun q hq => ?_,
    hctx.T_le (hctx.S_le hctx.mem_S)⟩
  exact hQz q hq

theorem sec11_normalizer_Q_le_centralizer_z [Finite G] (hp : Asc82Pre11) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    normalizer (secQ K1 K2 : Set G) ≤ centralizer ({z} : Set G) := by
  intro n hn
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  obtain ⟨hzQ, -, -, hQz, -⟩ := sec11_Q_facts hp hctx
  obtain ⟨-, hz2, -, -, hz1⟩ := sec11_invols hctx
  have hnQ := Subgroup.mem_normalizer_iff.mp hn
  have hnz : n * z * n⁻¹ ∈ secQ K1 K2 := (hnQ z).mp hzQ
  have hcen : ∀ q ∈ secQ K1 K2, (n * z * n⁻¹) * q = q * (n * z * n⁻¹) := by
    intro q hq
    have hq' : n⁻¹ * q * n ∈ secQ K1 K2 := by
      refine (hnQ _).mpr ?_
      simpa [mul_assoc] using hq
    have h1 := hQz _ hq'
    calc (n * z * n⁻¹) * q = n * (z * (n⁻¹ * q * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * q * n) * z) * n⁻¹ := by rw [h1]
      _ = q * (n * z * n⁻¹) := by group
  have hmem : n * z * n⁻¹ ∈ zpowers z :=
    sec10KS_Q_center hp.facts.pockets5 hp.facts.centZ5 hpsp hctx _ hnz hcen
  have hord : n * z * n⁻¹ ≠ 1 := by
    intro h
    exact hz1 (conj_eq_one_iff.mp h)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  have hkz : n * z * n⁻¹ = z := by
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · exfalso
      apply hord
      rw [← hk, hm, zpow_mul, hz2', one_zpow]
    · rw [← hk, hm, zpow_add, zpow_mul, hz2', one_zpow, one_mul, zpow_one]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by
    rw [mul_inv_eq_iff_eq_mul] at hkz
    exact hkz)

end CFSG.OddStandard.SmallF3.Omega
