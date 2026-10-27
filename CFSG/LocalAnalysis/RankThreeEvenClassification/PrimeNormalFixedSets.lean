module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalPermutationFixedSets
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem prime_card_subgroup_common_fixed_iff_generator {actor : Type u} {points : Type v}
    [Group actor] (action : actor →* Equiv.Perm points)
    (subgroup : Subgroup actor) (prime : ℕ) (hprime : prime.Prime)
    (hcard : Nat.card subgroup = prime) (generator : subgroup) (hne : generator ≠ 1)
    (point : points) :
    (∀ member : subgroup, action member point = point) ↔ action generator point = point := by
  have : Fact prime.Prime := ⟨hprime⟩
  constructor
  · exact fun hfixed => hfixed generator
  · intro hfixed member
    have hcyclic : Subgroup.zpowers generator = ⊤ := zpowers_eq_top_of_prime_card hcard hne
    have hmember : member ∈ Subgroup.zpowers generator := hcyclic.symm ▸ Subgroup.mem_top member
    obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmember
    have hpower : action (generator : actor) ^ exponent = action ((generator ^ exponent : subgroup) : actor) := by
      rw [← map_zpow]
      exact congrArg action (map_zpow subgroup.subtype generator exponent).symm
    rw [← hpower]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfixed exponent

theorem normal_prime_card_fixed_pair_invariant {actor : Type u} {points : Type v}
    [Group actor] (action : actor →* Equiv.Perm points)
    (normal : Subgroup actor) [normal.Normal]
    (prime : ℕ) (hprime : prime.Prime) (hcard : Nat.card normal = prime)
    (generator : normal) (hne : generator ≠ 1) (first second : points)
    (hfixed : ∀ point : points, action generator point = point ↔ point = first ∨ point = second) :
    ∀ member : actor, ∀ point : points,
      action member point ∈ ({first, second} : Set points) ↔ point ∈ ({first, second} : Set points) := by
  intro member point
  have hiff := normal_permutation_common_fixed_set_invariant action normal member point
  rw [prime_card_subgroup_common_fixed_iff_generator action normal prime hprime hcard generator hne,
    prime_card_subgroup_common_fixed_iff_generator action normal prime hprime hcard generator hne,
    hfixed, hfixed] at hiff
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hiff

theorem normal_small_card_prime_generated_centralizes {actor : Type u}
    [Group actor] [Finite actor] (normal : Subgroup actor) [normal.Normal]
    (prime : ℕ) (hprime : prime.Prime) (hsmall : Nat.card normal < prime)
    (hgenerated : Subgroup.closure {member : actor | ∃ exponent : ℕ,
      member ^ (prime ^ exponent) = 1} = ⊤) :
    ∀ member : actor, ∀ element : normal, member * (element : actor) = (element : actor) * member := by
  classical
  let : Fintype normal := Fintype.ofFinite normal
  let action : actor →* Equiv.Perm normal := (MulAut.toPerm normal).comp MulAut.conjNormal
  have hcoprime : ¬prime ∣ Nat.card (Equiv.Perm normal) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
    exact fun hdivides => (Nat.not_le_of_gt hsmall) ((hprime.dvd_factorial).mp hdivides)
  have htrivial := prime_generated_permutation_action_trivial_of_coprime_card
    action prime hprime hcoprime hgenerated
  intro member element
  have hfixed : MulAut.conjNormal member element = element :=
    DFunLike.congr_fun (htrivial member) element
  have hconjugate : member * (element : actor) * member⁻¹ = (element : actor) := by
    simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val hfixed
  calc
    member * (element : actor) = (member * (element : actor) * member⁻¹) * member := by group
    _ = (element : actor) * member := by rw [hconjugate]

end CFSG.RankThreeEvenClassification.Helpers
