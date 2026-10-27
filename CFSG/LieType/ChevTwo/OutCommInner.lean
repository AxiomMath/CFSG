module

public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LieType.ChevTwo

open CFSG.ComponentClassification.OuterAutomorphisms

theorem OutTwoNilpConcl.commutator_mem_inner {S : Type} [Group S] (h : OutTwoNilpConcl S)
    {δ : MulAut S} (hδ : Odd (orderOf δ))
    {Y : Subgroup (MulAut S)} (hY : IsPGroup 2 Y)
    (hδY : δ ∈ Subgroup.normalizer (Y : Set (MulAut S)))
    {y : MulAut S} (hy : y ∈ Y) :
    y⁻¹ * δ⁻¹ * y * δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  obtain ⟨N, hNnormal, -, hodd, hpow⟩ := h
  have hδN : δ ∈ N := by
    obtain ⟨k, hk⟩ := hpow δ
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hδ)).symm
    rw [← hm]
    exact N.pow_mem hk m
  have hcN : y⁻¹ * δ⁻¹ * y * δ ∈ N :=
    N.mul_mem (hNnormal.conj_mem δ⁻¹ (N.inv_mem hδN) y⁻¹) hδN
  have hcY : y⁻¹ * δ⁻¹ * y * δ ∈ Y := by
    have hconj : δ⁻¹ * y * δ ∈ Y := (Subgroup.mem_normalizer_iff''.mp hδY y).mp hy
    simpa only [mul_assoc] using Y.mul_mem (Y.inv_mem hy) hconj
  let I : Subgroup N := (CFSG.ComponentClassification.OuterAutomorphisms.inner S).subgroupOf N
  haveI hInormal : I.Normal :=
    Subgroup.Normal.subgroupOf (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S) N
  have hquotodd : Odd (Nat.card (N ⧸ I)) := by
    rw [← Subgroup.index_eq_card]
    exact hodd
  haveI : Finite (N ⧸ I) := Nat.finite_of_card_ne_zero hquotodd.pos.ne'
  let cN : N := ⟨y⁻¹ * δ⁻¹ * y * δ, hcN⟩
  let q : N ⧸ I := QuotientGroup.mk' I cN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hY) ⟨y⁻¹ * δ⁻¹ * y * δ, hcY⟩
  have hcop : Nat.Coprime (orderOf q) (2 ^ k) := by
    refine Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ?_)
    exact hquotodd.of_dvd_nat (orderOf_dvd_natCard q)
  have hcNorder : orderOf cN = 2 ^ k := by
    simpa only [cN, Subgroup.orderOf_mk] using hk
  have hdvd : orderOf q ∣ 2 ^ k := by
    have h1 : orderOf q ∣ orderOf cN := orderOf_map_dvd (QuotientGroup.mk' I) cN
    rwa [hcNorder] at h1
  have hq1 : q = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hcI : cN ∈ I := (QuotientGroup.eq_one_iff cN).mp hq1
  exact Subgroup.mem_subgroupOf.mp hcI

end CFSG.LieType.ChevTwo
