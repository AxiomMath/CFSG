module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem sec12fx_pow_mem {N : Subgroup G} {s n : G} (hs' : s⁻¹ ∈ normalizer (N : Set G))
    (hn : n ∈ N) (m : ℕ) : ∃ n' ∈ N, (s * n) ^ m = s ^ m * n' := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h⟩ := ih
    refine ⟨s⁻¹ * n' * s * n, N.mul_mem ?_ hn, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hs' n').1 hn'
    · rw [pow_succ, h, pow_succ]
      group

theorem sec12fx_le_of_alt {N S X : Subgroup G} (hS : IsPGroup 2 S)
    (hSN : S ≤ normalizer (N : Set G)) (hXY : X ≤ N ⊔ S)
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) : X ≤ N := by
  obtain ⟨e⟩ := hX
  haveI : IsSimpleGroup ↥X := e.isSimpleGroup
  have hYN : N ⊔ S ≤ normalizer (N : Set G) := sup_le Subgroup.le_normalizer hSN
  have hnorm : ((X ⊓ N).subgroupOf X).Normal := by
    constructor
    intro k hk x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hk ⊢
    obtain ⟨hkX, hkN⟩ := hk
    refine ⟨X.mul_mem (X.mul_mem x.2 hkX) (X.inv_mem x.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hYN (hXY x.2)) (k : G)).1 hkN
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X ⊓ N).subgroupOf X) with hbot | htop
  · exfalso
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Finite ↥X := Finite.of_equiv _ e.symm.toEquiv
    have hcard : Nat.card ↥X = 60 := by
      have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
      have h3 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]
        simp [Nat.factorial]
      rw [Nat.card_congr e.toEquiv]
      omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hcard]; norm_num)
    have hmem : (x : G) ∈ S ⊔ N := by
      rw [sup_comm]
      exact hXY x.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S N hSN] at hmem
    obtain ⟨s, hs, n, hn, hsn⟩ := hmem
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    have hsk : s ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    obtain ⟨n', hn', h⟩ := sec12fx_pow_mem (s := s) (Subgroup.mem_normalizer_iff.mpr fun m => by
      simpa using (Subgroup.mem_normalizer_iff.mp (hSN (S.inv_mem hs)) m)) hn (2 ^ k)
    have hxk : x ^ 2 ^ k ∈ (X ⊓ N).subgroupOf X := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨(x ^ 2 ^ k).2, ?_⟩
      rw [Subgroup.coe_pow, ← hsn, h, hsk, one_mul]
      exact hn'
    rw [hbot, Subgroup.mem_bot] at hxk
    have hdvd : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hxk
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  · intro x hx
    have h1 : (⟨x, hx⟩ : ↥X) ∈ (X ⊓ N).subgroupOf X := by
      rw [htop]
      trivial
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).2

end CFSG.OddStandard.SmallF3.Omega
