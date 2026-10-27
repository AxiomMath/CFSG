module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.BigOperators.Associated

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Equiv.Perm Equiv.Perm.OnCycleFactors

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem cycleType_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime) {σ : Equiv.Perm α} (hσ : σ ^ p = 1) :
    ∀ m ∈ σ.cycleType, m = p := by
  intro m hm
  have h1 : m ∣ orderOf σ := by
    rw [← Equiv.Perm.lcm_cycleType]
    exact Multiset.dvd_lcm hm
  have h2 : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hσ
  have h3 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
  rcases (Nat.dvd_prime hp).1 (h1.trans h2) with h | h
  · omega
  · exact h

theorem not_dvd_card_centralizer {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrp : r ≠ p) {σ : Equiv.Perm α} (hσ : σ ^ p = 1)
    (hsolv : Group.IsSolvable (Subgroup.centralizer {σ})) :
    ¬ r ∣ Nat.card (Subgroup.centralizer {σ}) := by
  have hct := cycleType_eq_of_pow_eq_one hp hσ
  set k := Multiset.card σ.cycleType with hk
  have hrep : σ.cycleType = Multiset.replicate k p := Multiset.eq_replicate_card.2 hct
  have hsum : σ.cycleType.sum = k * p := by rw [hrep]; simp [mul_comm]
  have hprod : σ.cycleType.prod = p ^ k := by rw [hrep]; simp
  have hfix : Fintype.card (Function.fixedPoints σ) = Fintype.card α - k * p := by
    rw [Equiv.Perm.card_fixedPoints, hsum]
  have hnsFix : Fintype.card (Function.fixedPoints σ) < 5 := by
    by_contra hge
    push Not at hge
    apply Equiv.Perm.not_isSolvable (Function.fixedPoints σ)
    · rw [Cardinal.mk_fintype]; exact_mod_cast hge
    · have hmem : ∀ u : Equiv.Perm (Function.fixedPoints σ),
          (ofSubtype u : Equiv.Perm α) ∈ Subgroup.centralizer {σ} := fun u => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Disjoint.commute (disjoint_iff_disjoint_support.mpr
          (ofSubtype_support_disjoint u)))
      let f : Equiv.Perm (Function.fixedPoints σ) →* Subgroup.centralizer {σ} :=
        (ofSubtype : Equiv.Perm (Function.fixedPoints σ) →* Equiv.Perm α).codRestrict _ hmem
      have hf : Function.Injective f := fun a b hab =>
        ofSubtype_injective (congrArg Subtype.val hab)
      exact Group.isSolvable_of_isSolvable_injective hf
  have hcyc : Fintype.card σ.cycleFactorsFinset = k := by
    rw [hk, Equiv.Perm.cycleType_def, Multiset.card_map]
    simp
  have hsurj : Function.Surjective (toPermHom σ) := by
    intro τ
    have : τ ∈ (toPermHom σ).range := by
      rw [mem_range_toPermHom_iff]
      intro c
      have h1 : c.val.support.card ∈ σ.cycleType := by
        rw [Equiv.Perm.cycleType_def]
        exact Multiset.mem_map.2 ⟨c.val, c.2, rfl⟩
      have h2 : (τ c).val.support.card ∈ σ.cycleType := by
        rw [Equiv.Perm.cycleType_def]
        exact Multiset.mem_map.2 ⟨(τ c).val, (τ c).2, rfl⟩
      rw [hct _ h1, hct _ h2]
    exact this
  have hnsK : k < 5 := by
    by_contra hge
    push Not at hge
    apply Equiv.Perm.not_isSolvable σ.cycleFactorsFinset
    · rw [Cardinal.mk_fintype, hcyc]; exact_mod_cast hge
    · exact Group.isSolvable_of_surjective hsurj
  intro hdvd
  rw [nat_card_centralizer, hsum, hprod] at hdvd
  have hrp' : Prime r := hr.prime
  rcases (hrp'.dvd_or_dvd hdvd) with h | h
  · rcases (hrp'.dvd_or_dvd h) with h | h
    · have := (Nat.Prime.dvd_factorial hr).1 h
      omega
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
  · obtain ⟨n, -, hn⟩ := (Prime.dvd_finsetProd_iff hrp' _).1 h
    have h1 := (Nat.Prime.dvd_factorial hr).1 hn
    have h2 : Multiset.count n σ.cycleType ≤ k := Multiset.count_le_card _ _
    omega

end CFSG.HardMathSupport.Curtis.Coordinator
