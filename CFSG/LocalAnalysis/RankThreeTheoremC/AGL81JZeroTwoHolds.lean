module

import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem exists_two_pow_mem_oUpperTwo {I : Subgroup G} {y : G} (hy : y ∈ I) :
    ∃ a : ℕ, y ^ (2 ^ a) ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨a, Subgroup.subset_closure ⟨I.pow_mem hy _, ?_⟩⟩
  have hdvd : 2 ^ a ∣ orderOf y := ⟨m, hn⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hn,
    Nat.mul_div_cancel_left m (pow_pos two_pos a)]
  exact hm

private theorem le_pCore_of_isSubnormal_of_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {S : Subgroup X} (hS : S.IsSubnormal) (hp : IsPGroup p S) :
    S ≤ CFSG.pCore p X := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = p} hS
  rw [← CFSG.pCore_eq_piCore ↥S p, ← CFSG.pCore_eq_piCore X p] at h
  have htop : CFSG.pCore p ↥S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.le.trans inf_le_right

theorem jOne_normal_jZero (H L : Subgroup G) : ((jOne H L).subgroupOf (jZero H L)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (jOne_le_jZero H L)).mpr
    ((jZero_le H L).trans (Subgroup.le_normalizer.trans (le_normalizer_jOne H L)))

theorem exists_two_pow_mem_jOne (H L : Subgroup G) {g : G} (hg : g ∈ jZero H L) :
    ∃ k : ℕ, g ^ (2 ^ k) ∈ jOne H L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := jOne_normal_jZero H L
  set J₀ := jZero H L with hJ₀
  set π := QuotientGroup.mk' ((jOne H L).subgroupOf J₀) with hπ
  have hmem : ∀ I ∈ cZero (H ⊓ L), (I.subgroupOf J₀).map π ≤
      CFSG.pCore 2 (↥J₀ ⧸ (jOne H L).subgroupOf J₀) := by
    intro I hI
    have hIJ : I ≤ J₀ := IsCZeroMember.le_jZero hI
    have hsub : CFSG.Open.IsSubnormal I J₀ := by
      have h := hI.subnormal.inf_of_le (jZero_le H L)
      rwa [inf_of_le_left hIJ] at h
    have hsubQ : ((I.subgroupOf J₀).map π).IsSubnormal := by
      have h1 := (CFSG.Open.IsSubnormal.of_mathlib
        (CFSG.Open.IsSubnormal.subgroupOf hsub)).map π
      rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at h1
      exact CFSG.Open.IsSubnormal.top_iff.mp h1
    have hp : IsPGroup 2 ((I.subgroupOf J₀).map π) := by
      rintro ⟨_, y, hy, rfl⟩
      obtain ⟨a, ha⟩ := exists_two_pow_mem_oUpperTwo (Subgroup.mem_subgroupOf.mp hy)
      refine ⟨a, Subtype.ext ?_⟩
      show π y ^ (2 ^ a) = 1
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact hI.oUpperTwo_le_jOne ha
    exact le_pCore_of_isSubnormal_of_isPGroup hsubQ hp
  have hJ₀ : J₀ ≤ ((CFSG.pCore 2 (↥J₀ ⧸ (jOne H L).subgroupOf J₀)).comap π).map J₀.subtype := by
    refine iSup₂_le fun I hI y hy => ?_
    have hyJ : y ∈ J₀ := IsCZeroMember.le_jZero hI hy
    exact ⟨⟨y, hyJ⟩, hmem I hI ⟨⟨y, hyJ⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hJ₀ hg
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥J₀ ⧸ (jOne H L).subgroupOf J₀) ⟨π x, hx⟩
  refine ⟨k, ?_⟩
  have hk' : π (x ^ (2 ^ k)) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  have h1 := (QuotientGroup.eq_one_iff _).mp hk'
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end CFSG.LocalAnalysis.RankThreeTheoremC
