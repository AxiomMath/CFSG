module

public import CFSG.CharacterTheory.Burnside.CharacterObstruction
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup

theorem relIndex_dvd_index_of_normal_right {G : Type*} [Group G] [Finite G] (A N : Subgroup G)
    [N.Normal] : A.relIndex N ∣ A.index := by
  have h1 : (A ⊓ N).relIndex A * A.relIndex (A ⊔ N) =
      (A ⊓ N).relIndex N * N.relIndex (A ⊔ N) := by
    rw [relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left,
      relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right]
  have h2 : (A ⊓ N).relIndex A = N.relIndex A := by rw [inf_comm, inf_relIndex_right]
  rw [h2, relIndex_sup_right, inf_relIndex_right, mul_comm (A.relIndex N)] at h1
  have h0 : N.relIndex A ≠ 0 := by
    rw [relIndex]
    exact index_ne_zero_of_finite
  have h3 : A.relIndex (A ⊔ N) = A.relIndex N :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) h1
  rw [← h3]
  exact relIndex_dvd_index_of_le le_sup_left

theorem eq_bot_of_isSimpleGroup_type {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnc : ¬ ∀ a b : G, a * b = b * a) (A : Subgroup G)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {k : ℕ} (hk : A.index = 2 ^ k) : A = ⊥ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  by_contra hx1
  have hAle : A ≤ centralizer {x} := by
    intro y hy
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hA w hx y hy
  have hdvd : Nat.card A ∣ Nat.card (MulAction.stabilizer (ConjAct G) x) := by
    rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer x]
    exact Subgroup.card_dvd_of_le hAle
  obtain ⟨t, ht⟩ := hdvd
  have : Fintype (MulAction.orbit (ConjAct G) x) := Fintype.ofFinite _
  have : Fintype (MulAction.stabilizer (ConjAct G) x) := Fintype.ofFinite _
  have horbit_mul : Nat.card (MulAction.orbit (ConjAct G) x) *
      Nat.card (MulAction.stabilizer (ConjAct G) x) = Nat.card G := by
    simpa only [Nat.card_eq_fintype_card, ConjAct.card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  have hG : Nat.card G = Nat.card A * 2 ^ k := by rw [← hk, Subgroup.card_mul_index]
  have h2 : Nat.card (MulAction.orbit (ConjAct G) x) * t = 2 ^ k := by
    have : Nat.card A * (Nat.card (MulAction.orbit (ConjAct G) x) * t) = Nat.card A * 2 ^ k := by
      rw [← hG, ← horbit_mul, ht]
      ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨t, h2.symm⟩
  apply CFSG.Burnside.CharacterObstruction.no_prime_pow_conjClass hnc x hx1 2 j Nat.prime_two
  rw [← ConjAct.orbit_eq_carrier_conjClasses x]
  exact hj

theorem eq_bot_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnc : ¬ ∀ a b : G, a * b = b * a) (A : Subgroup G)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {k : ℕ} (hk : A.index = 2 ^ k) : A = ⊥ := by
  obtain ⟨G', _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  have : IsSimpleGroup G' := e.isSimpleGroup_congr.mp inferInstance
  have hnc' : ¬ ∀ a b : G', a * b = b * a := fun h => hnc fun a b =>
    e.injective (by rw [map_mul, map_mul, h])
  have hA' : ∀ a ∈ A.map e.toMonoidHom, ∀ b ∈ A.map e.toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hA a ha b hb]
  have hk' : (A.map e.toMonoidHom).index = 2 ^ k := by
    rw [index_map_of_bijective e.bijective, hk]
  have := eq_bot_of_isSimpleGroup_type hnc' _ hA' hk'
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp this

theorem isSolvable_of_abelian_of_index_eq_two_pow {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {k : ℕ} (hk : A.index = 2 ^ k) :
    Group.IsSolvable G := by
  suffices H : ∀ (n : ℕ) (G : Type _) [Group G] [Finite G], Nat.card G = n →
      ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∃ k : ℕ, A.index = 2 ^ k) →
        Group.IsSolvable G from H _ G rfl A hA ⟨k, hk⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn A hA hk
  obtain ⟨k, hk⟩ := hk
  by_cases hsimple : IsSimpleGroup G
  · by_cases hcomm : ∀ a b : G, a * b = b * a
    · exact Group.isSolvable_of_comm hcomm
    · have hbot := eq_bot_of_isSimpleGroup hcomm A hA hk
      have hcard : Nat.card G = 2 ^ k := by rw [← hk, hbot, Subgroup.index_bot]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 G := IsPGroup.of_card hcard
      have := hp.isNilpotent
      infer_instance
  · by_cases hnt : Nontrivial G
    · rw [isSimpleGroup_iff] at hsimple
      simp only [hnt, true_and] at hsimple
      push Not at hsimple
      obtain ⟨N, hNnormal, hNbot, hNtop⟩ := hsimple
      have : N.Normal := hNnormal
      have hNlt : Nat.card N < n := by
        rw [← hn]
        exact lt_of_le_of_ne (N.card_le_card_group)
          (fun heq => hNtop (N.eq_top_of_le_card heq.ge))
      have hQlt : Nat.card (G ⧸ N) < n := by
        rw [← hn, N.card_eq_card_quotient_mul_card_subgroup]
        exact (Nat.lt_mul_iff_one_lt_right Nat.card_pos).2 ((N.one_lt_card_iff_ne_bot).2 hNbot)
      have hsN : Group.IsSolvable N := by
        refine ih _ hNlt N rfl (A.subgroupOf N) ?_ ?_
        · intro a ha b hb
          exact Subtype.ext (hA _ (mem_subgroupOf.mp ha) _ (mem_subgroupOf.mp hb))
        · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
            (hk ▸ relIndex_dvd_index_of_normal_right A N)
          exact ⟨j, hj⟩
      have hsQ : Group.IsSolvable (G ⧸ N) := by
        refine ih _ hQlt (G ⧸ N) rfl (A.map (QuotientGroup.mk' N)) ?_ ?_
        · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          rw [← map_mul, ← map_mul, hA a ha b hb]
        · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
            (hk ▸ index_map_dvd A (QuotientGroup.mk'_surjective N))
          exact ⟨j, hj⟩
      exact (Group.isSolvable_iff_subgroup_quotient N).2 ⟨hsN, hsQ⟩
    · have : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnt
      exact Group.isSolvable_of_comm fun _ _ => Subsingleton.elim _ _

end CFSG.GH74.Uniqueness.Hering
