module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem exists_conj_mem_of_card_prime {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {R S : Subgroup M} (hSR : S ≤ R) (hS : Nat.card S = p ^ (Nat.card R).factorization p)
    {t : M} (ht : t ∈ R) (htp : IsPGroup p (zpowers t)) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  let S' : Sylow p R := Sylow.ofCard (S.subgroupOf R) (by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv)
  have htR : IsPGroup p (zpowers (⟨t, ht⟩ : R)) := by
    have hcomap : (zpowers t).comap R.subtype = zpowers (⟨t, ht⟩ : R) := by
      ext r
      rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, Subtype.ext ?_⟩
        rwa [Subgroup.coe_zpow]
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        simpa [Subgroup.coe_zpow] using congrArg (Subtype.val : R → M) hk
    rw [← hcomap]
    exact htp.comap_subtype
  obtain ⟨T, hT⟩ := htR.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq R S' T
  refine ⟨x, x.2, ?_⟩
  have htT : (⟨t, ht⟩ : R) ∈ (T : Subgroup R) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htT
  obtain ⟨s, hs, hst⟩ := htT
  have hsS : (s : M) ∈ S := by
    have : s ∈ S.subgroupOf R := by
      rwa [show ((S' : Subgroup R)) = S.subgroupOf R from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨t, ht⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem exists_conj_mem_of_orderOf_eq_prime {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] {R S : Subgroup M} (hSR : S ≤ R)
    (hS : Nat.card S = p ^ (Nat.card R).factorization p) {t : M} (ht : t ∈ R)
    (htp : orderOf t = p) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  apply exists_conj_mem_of_card_prime hSR hS ht
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, htp, pow_one]

theorem exists_conj_mem_of_orderOf_eq_four {M : Type*} [Group M] [Finite M] {R S : Subgroup M}
    (hSR : S ≤ R) (hS : Nat.card S = 2 ^ (Nat.card R).factorization 2) {t : M} (ht : t ∈ R)
    (ht4 : orderOf t = 4) : ∃ x ∈ R, x⁻¹ * t * x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply exists_conj_mem_of_card_prime hSR hS ht
  apply IsPGroup.of_card (n := 2)
  rw [Nat.card_zpowers, ht4]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
