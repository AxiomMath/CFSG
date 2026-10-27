module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_commutator_mem_zpowers {U R : Subgroup G} {z : G} (hU : IsPGroup 2 U)
    (hRU : R ≤ U) (hUR : ∀ u ∈ U, ∀ r ∈ R, u * r * u⁻¹ ∈ R) (hzc : ∀ u ∈ U, u * z = z * u)
    (hne : ∃ r ∈ R, r ∉ zpowers z) :
    ∃ a ∈ R, a ∉ zpowers z ∧ ∀ u ∈ U, ⁅u, a⁆ ∈ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N0 : Subgroup ↥U := (zpowers z).subgroupOf U
  have hN0 : N0.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn
    have hg : Commute (g : G) z := (hzc g g.2)
    have hc : Commute (g : G) (n : G) := hk ▸ hg.zpow_right k
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ zpowers z
    rw [hc.mul_inv_cancel]
    exact hn
  let R1 : Subgroup ↥U := R.subgroupOf U
  have hR1 : R1.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hUR g g.2 n hn
  let R2 : Subgroup (↥U ⧸ N0) := R1.map (QuotientGroup.mk' N0)
  have hR2n : R2.Normal := Subgroup.Normal.map hR1 _ (QuotientGroup.mk'_surjective N0)
  have hQ : IsPGroup 2 (↥U ⧸ N0) := hU.of_surjective (QuotientGroup.mk' N0)
    (QuotientGroup.mk'_surjective N0)
  have : Group.IsNilpotent (↥U ⧸ N0) := hQ.isNilpotent
  obtain ⟨r, hr, hrz⟩ := hne
  have hR2 : R2 ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' N0 (⟨r, hRU hr⟩ : ↥U) ∈ R2 :=
      Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hr)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hrz (mem_subgroupOf.1 hmem)
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hR2
  obtain ⟨q, hq⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hinf
  have hqR2 : (q : ↥U ⧸ N0) ∈ R2 := (mem_inf.1 q.2).1
  have hqc : (q : ↥U ⧸ N0) ∈ center (↥U ⧸ N0) := (mem_inf.1 q.2).2
  obtain ⟨n, hn, hnq⟩ := hqR2
  refine ⟨(n : G), mem_subgroupOf.1 hn, ?_, ?_⟩
  · intro hz
    apply hq
    apply Subtype.ext
    rw [← hnq]
    exact (QuotientGroup.eq_one_iff n).2 (mem_subgroupOf.2 hz)
  · intro u hu
    have hcomm : (QuotientGroup.mk' N0) ⁅(⟨u, hu⟩ : ↥U), n⁆ = 1 := by
      rw [map_commutatorElement, QuotientGroup.mk'_apply, hnq]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (mem_center_iff.1 hqc (QuotientGroup.mk (⟨u, hu⟩ : ↥U)))
    have := (QuotientGroup.eq_one_iff _).1 hcomm
    exact mem_subgroupOf.1 this

end CFSG.EvenSporadicStandard.TwoB
