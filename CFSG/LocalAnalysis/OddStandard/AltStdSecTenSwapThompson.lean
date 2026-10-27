module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFPT

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

variable {G : Type*} [Group G]

theorem not_two_dvd_index_of_normalizer_le [Finite G] {T H : Subgroup G} (hT : IsPGroup 2 T)
    (hH : normalizer (T : Set G) ≤ H) {a : ℕ} (hTcard : Nat.card T = 2 ^ a)
    (hHcard : ¬ 2 ^ (a + 1) ∣ Nat.card H) : ¬ 2 ∣ T.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hd
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  by_cases hTPeq : T = (P : Subgroup G)
  · rw [hTPeq] at hd
    exact P.not_dvd_index hd
  · have hTPlt : T < (P : Subgroup G) := lt_of_le_of_ne hTP hTPeq
    haveI : Group.IsNilpotent (↥(P : Subgroup G)) := P.isPGroup'.isNilpotent
    have hNC : NormalizerCondition (↥(P : Subgroup G)) :=
      Group.normalizerCondition_of_isNilpotent
    have hproper : T.subgroupOf (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      exact hTPeq (le_antisymm hTP (Subgroup.subgroupOf_eq_top.mp h))
    obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt (hNC (T.subgroupOf (P : Subgroup G)) hproper)
    have hxN' : (x : G) ∈ normalizer (T : Set G) := by
      have hEq := Subgroup.subgroupOf_normalizer_eq hTP
      rw [← hEq] at hxN
      exact Subgroup.mem_subgroupOf.1 hxN
    have hxnT : (x : G) ∉ T := fun h => hxT (Subgroup.mem_subgroupOf.2 h)
    let M : Subgroup G := (P : Subgroup G) ⊓ normalizer (T : Set G)
    have hTM : T ≤ M := fun t ht => ⟨hTP ht, Subgroup.le_normalizer ht⟩
    have hxM : (x : G) ∈ M := ⟨x.2, hxN'⟩
    have hTltM : T < M := by
      refine lt_of_le_of_ne hTM ?_
      intro hTM'
      rw [← hTM'] at hxM
      exact hxnT hxM
    have hMH : M ≤ H := fun m hm => hH hm.2
    have hM2 : IsPGroup 2 M := P.isPGroup'.to_le inf_le_left
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2) (G := M)).1 hM2
    have hlt : a < b := by
      have h1 : 2 ^ a < Nat.card M := by
        rw [← hTcard]
        exact Subgroup.card_lt_of_lt hTltM
      rw [hb] at h1
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
    have hdivM : 2 ^ (a + 1) ∣ Nat.card M := by
      rw [hb]
      exact pow_dvd_pow 2 (Nat.succ_le_iff.mpr hlt)
    exact hHcard (hdivM.trans (Subgroup.card_dvd_of_le hMH))

theorem false_of_thompson_involution [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {z : G}
    (hz : orderOf z = 2) (hzT : z ∈ T) (hzU : z ∉ U) (hconj : ∀ g : G, g⁻¹ * z * g ∉ U) :
    False := by
  have hmin : ∀ y ∈ T, y ∉ U → orderOf z ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h1 => hyU (h1 ▸ U.one_mem)
    rw [hz]
    have h1 := orderOf_pos y
    have h2 : orderOf y ≠ 1 := fun h3 => hy1 (orderOf_eq_one_iff.1 h3)
    omega
  obtain ⟨N, hN, hidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
    (T := T) (U := U) hT hTidx hUT hUidx hzT hzU hmin hconj
  haveI : N.Normal := hN
  exact false_of_simple_of_index_two hnonab hidx

end CFSG.OddStandard.AltStdSec.SwapPattern
