module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111Na
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec11cSplit (t z : G) (K1 K2 : Subgroup G) : Prop where
  split : IsDirectSplit (oddCoreIn (secK0 t z)) (K1 ⊔ K2) (secK0 t z)
  conjQ : ∀ k ∈ K1 ⊔ K2, ∀ q ∈ secQ K1 K2, k * q * k⁻¹ ∈ secQ K1 K2
  Q_le : secQ K1 K2 ≤ K1 ⊔ K2
  z_mem : z ∈ K1 ⊔ K2
  z_sq : z * z = 1
  z_comm : ∀ g ∈ secK0 t z, g * z = z * g
  cent : ∀ g ∈ secK0 t z, (∀ q ∈ secQ K1 K2, g * q = q * g) →
    ∃ n ∈ oddCoreIn (secK0 t z), ∃ e ∈ zpowers z, g = n * e

theorem sec11c_split_of [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) : Sec11cSplit t z K1 K2 := by
  have hP5 : Asc82FactPockets5 := hp.facts.pockets5
  have hC5 : Asc82FactCentZ5 := hp.facts.centZ5
  have hbas := hp.basic G t L S z hctx.toSec10Z
  have hpsp : IsPSp43 L := hbas.1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  refine ⟨sec10A2_split hp.s3 hp.r10.toAsc82Res10a hp.facts hp.basic hctx,
    fun k hk q hq => sec11_conj_mem_Q hk hq, sec11_Q_le_sup K1 K2,
    sec11_Q_le_sup K1 K2 (sec10KS_Q_elem hP5 hC5 hpsp hctx).1, ?_,
    fun g hg => Subgroup.mem_centralizer_singleton_iff.1 ((sec11_K0_le t z hg).2),
    fun g hg hc => sec11_cent_K0_Q hp.r10.lK0 hP5 hC5 hpsp hctx hg hc⟩
  rw [← pow_two, ← hz2]
  exact pow_orderOf_eq_one z

theorem sec11c_two_odd {e : G} (he2 : e ^ 2 = 1) {B : ℕ} (hB : Odd B) (heB : e ^ B = 1) :
    e = 1 := by
  have h1 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one he2
  have h2 : orderOf e ∣ B := orderOf_dvd_of_pow_eq_one heB
  have h3 : orderOf e ∣ Nat.gcd 2 B := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 2 B = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hB)
  rw [h4] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

namespace Sec11cSplit

variable {t z : G} {K1 K2 : Subgroup G}

theorem comm' (hS : Sec11cSplit t z K1 K2) {n k : G} (hn : n ∈ oddCoreIn (secK0 t z))
    (hk : k ∈ K1 ⊔ K2) : k * n = n * k :=
  (hS.split.comm n hn k hk).symm

theorem conj_K0_Q (hS : Sec11cSplit t z K1 K2) {g : G} (hg : g ∈ secK0 t z) {q : G}
    (hq : q ∈ secQ K1 K2) : g * q * g⁻¹ ∈ secQ K1 K2 := by
  obtain ⟨n, hn, k, hk, rfl⟩ := hS.split.dec g hg
  have hkq : k * q * k⁻¹ ∈ secQ K1 K2 := hS.conjQ k hk q hq
  have hc : n * (k * q * k⁻¹) = (k * q * k⁻¹) * n := hS.split.comm n hn _ (hS.Q_le hkq)
  have e : n * k * q * (n * k)⁻¹ = k * q * k⁻¹ := by
    calc n * k * q * (n * k)⁻¹ = n * (k * q * k⁻¹) * n⁻¹ := by group
      _ = (k * q * k⁻¹) * n * n⁻¹ := by rw [hc]
      _ = k * q * k⁻¹ := by group
  rw [e]
  exact hkq

theorem proj_pow (hS : Sec11cSplit t z K1 K2) {n κ : G} (hn : n ∈ oddCoreIn (secK0 t z))
    (hκ : κ ∈ K1 ⊔ K2) {b : ℕ} (hb : (n * κ) ^ b = 1) : κ ^ b = 1 := by
  have hcomm : Commute n κ := hS.split.comm n hn κ hκ
  rw [hcomm.mul_pow] at hb
  have hmem : κ ^ b ∈ oddCoreIn (secK0 t z) := by
    rw [eq_inv_of_mul_eq_one_right hb]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hn b)
  exact hS.split.disj _ hmem (Subgroup.pow_mem _ hκ b)

theorem quot_mem [Finite G] (hS : Sec11cSplit t z K1 K2) {k k' : G} (hk : k ∈ secK0 t z)
    (hk' : k' ∈ secK0 t z) (hko : Odd (orderOf k)) (hko' : Odd (orderOf k'))
    (hc : ∀ q ∈ secQ K1 K2, (k⁻¹ * k') * q = q * (k⁻¹ * k')) :
    k⁻¹ * k' ∈ oddCoreIn (secK0 t z) := by
  have hw : k⁻¹ * k' ∈ secK0 t z := Subgroup.mul_mem _ (Subgroup.inv_mem _ hk) hk'
  obtain ⟨n', hn', e, he, hwe⟩ := hS.cent _ hw hc
  obtain ⟨n₁, hn₁, κ, hκ, rfl⟩ := hS.split.dec k hk
  obtain ⟨n₂, hn₂, κ', hκ', rfl⟩ := hS.split.dec k' hk'
  have hdec : (n₁ * κ)⁻¹ * (n₂ * κ') = (n₁⁻¹ * n₂) * (κ⁻¹ * κ') := by
    have h1 : κ⁻¹ * n₁⁻¹ = n₁⁻¹ * κ⁻¹ :=
      hS.comm' (Subgroup.inv_mem _ hn₁) (Subgroup.inv_mem _ hκ)
    have h2 : κ⁻¹ * n₂ = n₂ * κ⁻¹ := hS.comm' hn₂ (Subgroup.inv_mem _ hκ)
    calc (n₁ * κ)⁻¹ * (n₂ * κ') = (κ⁻¹ * n₁⁻¹) * n₂ * κ' := by group
      _ = n₁⁻¹ * (κ⁻¹ * n₂) * κ' := by rw [h1]; group
      _ = n₁⁻¹ * (n₂ * κ⁻¹) * κ' := by rw [h2]
      _ = (n₁⁻¹ * n₂) * (κ⁻¹ * κ') := by group
  have hzK : zpowers z ≤ K1 ⊔ K2 := Subgroup.zpowers_le.2 hS.z_mem
  have huniq := hS.split.unique (n := n₁⁻¹ * n₂) (n' := n') (k := κ⁻¹ * κ') (k' := e)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₁) hn₂) hn'
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ) hκ') (hzK he) (by rw [← hdec, hwe])
  have hκe : κ⁻¹ * κ' = e := huniq.2
  have hκ'e : κ' = κ * e := by rw [← hκe]; group
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 he
  have hκz : Commute κ z := hS.z_comm κ (hS.split.right_le hκ)
  have hκe_comm : Commute κ e := by rw [← hj]; exact hκz.zpow_right j
  have he2 : e ^ 2 = 1 := by
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hS.z_sq
    simp [hz2]
  set b := orderOf (n₁ * κ) with hb
  set b' := orderOf (n₂ * κ') with hb'
  have hκb : κ ^ b = 1 := hS.proj_pow hn₁ hκ (pow_orderOf_eq_one _)
  have hκb' : κ' ^ b' = 1 := hS.proj_pow hn₂ hκ' (pow_orderOf_eq_one _)
  have hBodd : Odd (b * b') := hko.mul hko'
  have hκB : κ ^ (b * b') = 1 := by rw [pow_mul, hκb, one_pow]
  have hκ'B : κ' ^ (b * b') = 1 := by rw [mul_comm, pow_mul, hκb', one_pow]
  have heB : e ^ (b * b') = 1 := by
    have h := hκ'B
    rw [hκ'e, hκe_comm.mul_pow, hκB, one_mul] at h
    exact h
  have he1 : e = 1 := sec11c_two_odd he2 hBodd heB
  rw [hdec, hκe, he1, mul_one]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₁) hn₂

end Sec11cSplit

end CFSG.OddStandard.SmallF3.Omega
