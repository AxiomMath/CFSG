module

public import CFSG.GH74.GLS.TwoThin.Basic

public section

open Subgroup

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

theorem pPrimeCoreOf_sup_le {G : Type} [Group G] [Finite G] {H U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hUH : U ≤ normalizer (H : Set G)) :
    pPrimeCoreOf 2 (H ⊔ U) ≤ pPrimeCoreOf 2 H := by
  have hHS : H ≤ H ⊔ U := le_sup_left
  have hSn : H ⊔ U ≤ normalizer (H : Set G) := sup_le le_normalizer hUH
  have hnormal : (H.subgroupOf (H ⊔ U)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSn
  let q : ↥(H ⊔ U) →* ↥(H ⊔ U) ⧸ H.subgroupOf (H ⊔ U) := QuotientGroup.mk' _
  have hOH : pPrimeCoreOf 2 (H ⊔ U) ≤ H := by
    intro o ho
    have hoS : o ∈ H ⊔ U := TwoThin.pPrimeCoreOf_le _ ho
    have h : o ∈ ((U ⊔ H : Subgroup G) : Set G) := by rwa [sup_comm]
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U H hUH] at h
    obtain ⟨z, hz, k, hk, hzk⟩ := h
    have hzS : z ∈ H ⊔ U := Subgroup.mem_sup_right hz
    have hq : q ⟨z, hzS⟩ = q ⟨o, hoS⟩ := by
      simp only [q, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      simpa [← hzk] using hk
    obtain ⟨a, ha⟩ := hU2 ⟨z, hz⟩
    have hza : q ⟨z, hzS⟩ ^ (2 ^ a) = 1 := by
      have : (⟨z, hzS⟩ : ↥(H ⊔ U)) ^ (2 ^ a) = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val ha)
      rw [← map_pow, this, map_one]
    have hodd : Odd (orderOf (⟨o, hoS⟩ : ↥(H ⊔ U))) := by
      rw [Subgroup.orderOf_mk]
      exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) (Subgroup.orderOf_dvd_natCard _ ho)
    have h1 : orderOf (q ⟨o, hoS⟩) ∣ 2 ^ a := by
      rw [← hq]
      exact orderOf_dvd_of_pow_eq_one hza
    have h2 : orderOf (q ⟨o, hoS⟩) ∣ orderOf (⟨o, hoS⟩ : ↥(H ⊔ U)) := orderOf_map_dvd _ _
    have h3 : orderOf (q ⟨o, hoS⟩) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right a) h2 h1
    have h4 : q ⟨o, hoS⟩ = 1 := orderOf_eq_one_iff.mp h3
    have h5 : (⟨o, hoS⟩ : ↥(H ⊔ U)) ∈ H.subgroupOf (H ⊔ U) := (QuotientGroup.eq_one_iff _).mp h4
    exact Subgroup.mem_subgroupOf.mp h5
  have hnormO : ∀ x ∈ H, ∀ n ∈ pPrimeCoreOf 2 (H ⊔ U), x * n * x⁻¹ ∈ pPrimeCoreOf 2 (H ⊔ U) :=
    fun x hx n hn => TwoThin.pPrimeCoreOf_normalized _ (hHS hx) hn
  have hnormal' : ((pPrimeCoreOf 2 (H ⊔ U)).subgroupOf H).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnormO (h : G) h.2 (a : G) ha⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCoreOf 2 (H ⊔ U)).subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
    exact Nat.coprime_two_left.2 (TwoThin.card_pPrimeCoreOf_odd _)
  have hle : (pPrimeCoreOf 2 (H ⊔ U)).subgroupOf H ≤ pPrimeCore 2 ↥H := le_sSup ⟨hnormal', hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hOH]
  exact Subgroup.map_mono hle

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
