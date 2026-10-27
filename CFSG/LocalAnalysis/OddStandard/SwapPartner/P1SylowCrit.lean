module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

theorem exists_fixedPoint_of_pow_two_pow_eq_one {α : Type*} [Finite α]
    (hodd : Odd (Nat.card α)) (f : Equiv.Perm α) {m : ℕ} (hf : f ^ 2 ^ m = 1) :
    ∃ a, f a = a := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  exact Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := m) hnd hf

variable {G : Type} [Group G]

theorem not_two_dvd_index_of_two_elements [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    {a : ℕ} (hTcard : Nat.card T = 2 ^ a)
    (h : ∀ x ∈ normalizer (T : Set G), (∃ m : ℕ, x ^ 2 ^ m = 1) →
      ∃ H : Subgroup G, T ≤ H ∧ x ∈ H ∧ ¬ 2 ^ (a + 1) ∣ Nat.card H) :
    ¬ 2 ∣ T.index := by
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
      intro hh
      exact hTPeq (le_antisymm hTP (Subgroup.subgroupOf_eq_top.mp hh))
    obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt (hNC (T.subgroupOf (P : Subgroup G)) hproper)
    have hxN' : (x : G) ∈ normalizer (T : Set G) := by
      have hEq := Subgroup.subgroupOf_normalizer_eq hTP
      rw [← hEq] at hxN
      exact Subgroup.mem_subgroupOf.1 hxN
    have hxnT : (x : G) ∉ T := fun hh => hxT (Subgroup.mem_subgroupOf.2 hh)
    have hxP : (x : G) ∈ (P : Subgroup G) := x.2
    have hx2 : ∃ m : ℕ, (x : G) ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := P.isPGroup' x
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    obtain ⟨H, hTH, hxH, hHcard⟩ := h (x : G) hxN' hx2
    let M : Subgroup G := T ⊔ Subgroup.zpowers (x : G)
    have hTM : T ≤ M := le_sup_left
    have hxM : (x : G) ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G))
    have hTltM : T < M := by
      refine lt_of_le_of_ne hTM ?_
      intro hTM'
      rw [← hTM'] at hxM
      exact hxnT hxM
    have hMP : M ≤ (P : Subgroup G) := sup_le hTP (Subgroup.zpowers_le.2 hxP)
    have hM2 : IsPGroup 2 M := P.isPGroup'.to_le hMP
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
    have hMH : M ≤ H := sup_le hTH (Subgroup.zpowers_le.2 hxH)
    exact hHcard (hdivM.trans (Subgroup.card_dvd_of_le hMH))

variable {z : G} {ι : Perm (Fin 10) →* G}

theorem card_centralizer_of_centData (hC : CentData z ι) :
    Nat.card ↥(centralizer ({z} : Set G)) = 2 * Nat.card (Perm (Fin 10)) := by
  have h := hC.card_inf_centralizer (1 : Perm (Fin 10))
  rw [map_one] at h
  have hG : centralizer ({1} : Set G) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
    exact Subgroup.mem_center_iff.2 fun g => by simp
  have hP : centralizer ({1} : Set (Perm (Fin 10))) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
    exact Subgroup.mem_center_iff.2 fun g => by simp
  rw [hG, hP, inf_top_eq, Subgroup.card_top] at h
  exact h

end CFSG.OddStandard.AltStdSec.SwapPartner
