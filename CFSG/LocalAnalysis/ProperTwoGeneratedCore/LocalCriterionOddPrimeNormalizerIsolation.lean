module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

theorem odd_prime_subgroup_card_odd (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (M : Subgroup G) (hM : IsPGroup p M) : Odd (Nat.card M) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  rw [hn]
  exact hodd.pow

theorem local_point_odd_subgroup_normalizer_class_isolation
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (M : Subgroup G) (hModd : Odd (Nat.card M))
    (hzM : z ∈ Subgroup.normalizer (M : Set G)) (hMH : ¬ M ≤ H)
    {s : G} (hs : s ∈ involutionPointClass z)
    (hsM : s ∈ Subgroup.normalizer (M : Set G)) (hcomm : Commute s z) : s = z := by
  by_contra hne
  apply hMH
  exact local_point_odd_subgroup_le_of_commuting_class h hs hcomm.symm hne M hModd
    (sup_le (Subgroup.zpowers_le.mpr hzM) (Subgroup.zpowers_le.mpr hsM))

theorem local_point_odd_prime_normalizer_class_isolation
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (M : Subgroup G) (hM : IsPGroup p M)
    (hzM : z ∈ Subgroup.normalizer (M : Set G)) (hMH : ¬ M ≤ H)
    {s : G} (hs : s ∈ involutionPointClass z)
    (hsM : s ∈ Subgroup.normalizer (M : Set G)) (hcomm : Commute s z) : s = z :=
  local_point_odd_subgroup_normalizer_class_isolation h M
    (odd_prime_subgroup_card_odd p hp hodd M hM) hzM hMH hs hsM hcomm

end CFSG.ProperTwoGeneratedCore
