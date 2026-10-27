module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog.Section3
open CFSG.Sporadic.SmallOddCore
open Subgroup

theorem stab_eq_of_le {G : Type} [Group G] [Finite G] {ι : Type} [Fintype ι]
    (K : Subgroup G) (B : Set G) (T : ι → Set G) (c : ι → G) (n : ι → ℕ)
    (hsub : ∀ i, T i ⊆ B) (hdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hinv : ∀ i, ∀ k ∈ K, ∀ x ∈ T i, k * x * k⁻¹ ∈ T i)
    (hc : ∀ i, c i ∈ T i) (hle : ∀ i, Nat.card ↥(K ⊓ Gx (c i)) ≤ n i)
    (hdvd : ∀ i, n i ∣ Nat.card K) (hsum : ∑ i, Nat.card K / n i = B.ncard) :
    ∀ i, Nat.card ↥(K ⊓ Gx (c i)) = n i := by
  classical
  let O : ι → Set G := fun i => conjClass K (c i)
  have hO_sub_T : ∀ i, O i ⊆ T i := by
    intro i x hx
    obtain ⟨k, hk, rfl⟩ := mem_conjClass.mp hx
    exact hinv i k hk (c i) (hc i)
  have hO_disj : Pairwise (fun i j => Disjoint (O i) (O j)) := by
    intro i j hij
    exact (hdisj i j hij).mono (hO_sub_T i) (hO_sub_T j)
  have hmul : ∀ i, (O i).ncard * Nat.card ↥(K ⊓ Gx (c i)) = Nat.card K := fun i =>
    ncard_conjClass_mul_card K (c i)
  have hspos : ∀ i, 0 < Nat.card ↥(K ⊓ Gx (c i)) := by
    intro i
    haveI : Nonempty ↥(K ⊓ Gx (c i)) := ⟨1⟩
    exact Nat.card_pos
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hge : ∀ i, Nat.card K / n i ≤ (O i).ncard := by
    intro i
    refine Nat.div_le_of_le_mul ?_
    rw [← hmul i, Nat.mul_comm (n i)]
    exact Nat.mul_le_mul_left _ (hle i)
  have hU : (⋃ i, O i).ncard = ∑ i, (O i).ncard := by
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite (O i)) hO_disj,
      finsum_eq_sum_of_fintype]
  have hUB : (⋃ i, O i).ncard ≤ B.ncard :=
    Set.ncard_le_ncard (Set.iUnion_subset fun i => (hO_sub_T i).trans (hsub i)) (Set.toFinite B)
  have hall : ∀ i ∈ Finset.univ, Nat.card K / n i = (O i).ncard := by
    refine (Finset.sum_eq_sum_iff_of_le (fun i _ => hge i)).1 (le_antisymm
      (Finset.sum_le_sum fun i _ => hge i) ?_)
    rw [← hU, hsum]
    exact hUB
  intro i
  have hOi := hall i (Finset.mem_univ i)
  obtain ⟨q, hq⟩ := hdvd i
  have hn : 0 < n i := lt_of_lt_of_le (hspos i) (hle i)
  have hqv : Nat.card K / n i = q := by rw [hq, Nat.mul_div_cancel_left q hn]
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, Nat.mul_zero] at hq
      omega
    · exact h
  have e1 : (O i).ncard = q := by rw [← hOi, hqv]
  have e : q * Nat.card ↥(K ⊓ Gx (c i)) = q * n i := by
    rw [← e1, hmul i, hq, e1, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hqpos e

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
