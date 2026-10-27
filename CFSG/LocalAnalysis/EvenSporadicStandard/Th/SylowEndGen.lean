module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Basic

public section

namespace CFSG.EvenSporadicStandard.ThStd.SylowEnd

open Subgroup CFSG.GH74.GLS.Bg.Thompson

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf {H K : Subgroup G} (hH : H ≤ normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have hN1 : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hH
  have hN2 : (K.subgroupOf (H ⊔ K)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hH
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf H)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K))
  have h3 : Nat.card ↥(K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [← inf_subgroupOf_right K H, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ K ≤ H)).toEquiv
  have h4 : Nat.card ↥(K.subgroupOf (H ⊔ K)) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ H ⊔ K)).toEquiv
  have h5 : Nat.card (↥H ⧸ K.subgroupOf H) = Nat.card (↥(H ⊔ K) ⧸ K.subgroupOf (H ⊔ K)) :=
    Nat.card_congr e.toEquiv
  rw [h3] at h1
  rw [h4] at h2
  rw [h2, h1, ← h5]
  ring

theorem card_le_of_isSylowIn [Finite G] {R Y Q : Subgroup G} (hR : IsSylowIn 2 R Y)
    (hQY : Q ≤ Y) (hQ : IsPGroup 2 Q) : Nat.card Q ≤ Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRY, hR2, hRidx⟩ := hR
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hR2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  have hY : R.relIndex Y * Nat.card R = Nat.card Y := by
    have := Subgroup.relIndex_mul_card R Y
    rwa [inf_of_le_left hRY] at this
  have hdvd : 2 ^ k ∣ R.relIndex Y * 2 ^ m := by
    rw [← hk, ← hm, hY]
    exact Subgroup.card_dvd_of_le hQY
  have hcop : Nat.Coprime (2 ^ k) (R.relIndex Y) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hRidx)
  have h2 : 2 ^ k ∣ 2 ^ m := hcop.dvd_of_dvd_mul_left hdvd
  have hkm : k ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  rw [hk, hm]
  exact Nat.pow_le_pow_right (by norm_num) hkm

theorem sup_zpowers_comm {E : Subgroup G} {v : G} (hc : ∀ x ∈ E, x * v = v * x)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∀ x ∈ E ⊔ zpowers v, ∀ y ∈ E ⊔ zpowers v, x * y = y * x := by
  have hcomm : zpowers v ≤ centralizer (E : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => hc y hy
  intro x hx y hy
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_mul_of_mem_sup hcomm hx
  obtain ⟨a', ha', r', hr', rfl⟩ := exists_mul_of_mem_sup hcomm hy
  have h1 : Commute r a' := (mem_centralizer_iff.1 (hcomm hr) a' ha').symm
  have h2 : Commute a r' := (mem_centralizer_iff.1 (hcomm hr') a ha)
  have h3 : Commute r r' := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr'
    exact (Commute.refl v).zpow_zpow i j
  have h4 : Commute a a' := hE a ha a' ha'
  exact ((h4.mul_right h2).mul_left (h1.mul_right h3)).eq

theorem sup_zpowers_sq {E : Subgroup G} {v : G} (hv : v ^ 2 = 1) (hc : ∀ x ∈ E, x * v = v * x)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) :
    ∀ x ∈ E ⊔ zpowers v, x ^ 2 = 1 := by
  have hcomm : zpowers v ≤ centralizer (E : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => hc y hy
  intro x hx
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_mul_of_mem_sup hcomm hx
  have h1 : Commute a r := mem_centralizer_iff.1 (hcomm hr) a ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  rw [h1.mul_pow, hE2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hv, one_zpow]

theorem arith_lb {q k p r s : ℕ} (hprod : q * k = r * 2 ^ 12) (hle : q ≤ p)
    (hP : p * 2 ^ 9 = 2 ^ 14 * s) (hr : 2 * s ≤ r) (hp : 0 < p) : 2 ^ 8 ≤ k := by
  by_contra hlt
  push Not at hlt
  have h1 : q * k ≤ p * k := Nat.mul_le_mul_right _ hle
  have h2 : p * k < p * 2 ^ 8 := Nat.mul_lt_mul_of_pos_left hlt hp
  have e12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have e9 : (2 : ℕ) ^ 9 = 512 := by norm_num
  have e14 : (2 : ℕ) ^ 14 = 16384 := by norm_num
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [e12] at hprod
  rw [e9, e14] at hP
  rw [e8] at h2
  omega

end CFSG.EvenSporadicStandard.ThStd.SylowEnd
