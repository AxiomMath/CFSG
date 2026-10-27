module

public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.EvenSporadicStandard.TwoHS.SignS9

open Equiv Equiv.Perm
open scoped Finset

section CycleType

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_eq_two_two (hα : Fintype.card α = 9) {τ : Perm α} (h1 : τ ≠ 1)
    (h2 : τ * τ = 1) (hc : Nat.card (Subgroup.centralizer {τ}) = 960) :
    τ.cycleType = {2, 2} := by
  have hord : orderOf τ = 2 := orderOf_eq_prime (by rwa [pow_two]) h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := τ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : τ.cycleType.sum ≤ Fintype.card α := sum_cycleType_le τ
  rw [nat_card_centralizer, hn, hα] at hc
  rw [hn, Multiset.sum_replicate, hα] at hsum
  have hn4 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by simp at hsum; omega
  rcases hn4 with rfl | rfl | rfl | rfl
  · simp [Nat.factorial] at hc
  · rw [hn]
    rfl
  · simp [Nat.factorial] at hc
  · simp [Nat.factorial] at hc

theorem card_support_of_cycleType_eq_two_two {τ : Perm α} (h : τ.cycleType = {2, 2}) :
    #τ.support = 4 := by
  rw [← sum_cycleType, h]
  rfl

theorem card_fixedPoints_of_cycleType_eq_two_two (hα : Fintype.card α = 9) {τ : Perm α}
    (h : τ.cycleType = {2, 2}) : Fintype.card (Function.fixedPoints τ) = 5 := by
  rw [card_fixedPoints, h, hα]
  rfl

theorem sign_eq_one_of_cycleType_eq_two_two {τ : Perm α} (h : τ.cycleType = {2, 2}) :
    sign τ = 1 := by
  rw [sign_of_cycleType, h]
  decide

theorem sign_eq_neg_one_of_orderOf_eq_four {d : Perm α} (h4 : orderOf d = 4)
    (hs : #d.support ≤ 4) : sign d = -1 := by
  have hm : ∀ n ∈ d.cycleType, n = 2 ∨ n = 4 := by
    intro n hn
    have h1 : n ∣ 4 := h4 ▸ dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := two_le_of_mem_cycleType hn
    have h3 : n ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    have : n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd h1 (by norm_num)
    · exact Or.inr rfl
  have h4mem : 4 ∈ d.cycleType := by
    by_contra hno
    have : d.cycleType.lcm ∣ 2 := Multiset.lcm_dvd.2 fun n hn => by
      rcases hm n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn hno
    rw [lcm_cycleType, h4] at this
    omega
  obtain ⟨m, hm'⟩ := Multiset.exists_cons_of_mem h4mem
  have hsum : d.cycleType.sum ≤ 4 := (sum_cycleType d).le.trans hs
  rw [hm', Multiset.sum_cons] at hsum
  have hm0 : m = 0 := by
    have : m.sum = 0 := by omega
    rw [Multiset.sum_eq_zero_iff] at this
    refine Multiset.eq_zero_of_forall_notMem fun n hn => ?_
    have := this n hn
    have h2 := two_le_of_mem_cycleType (hm' ▸ Multiset.mem_cons_of_mem hn : n ∈ d.cycleType)
    omega
  rw [sign_of_cycleType, hm', hm0]
  simp only [Multiset.sum_cons, Multiset.sum_zero, Multiset.card_cons, Multiset.card_zero]
  exact Odd.neg_one_pow (by decide)

end CycleType

section FixRestrict

variable {α : Type*}

@[expose] def fixRestrict [Fintype α] [DecidableEq α] (τ : Perm α) :
    Subgroup.centralizer ({τ} : Set (Perm α)) →* Perm (Function.fixedPoints τ) where
  toFun g := (g : Perm α).subtypePerm
    (fun _ => apply_mem_fixedPoints_iff_mem_of_mem_centralizer g.2)
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

variable [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem ofSubtype_mem_centralizer (τ : Perm α) (u : Perm (Function.fixedPoints τ)) :
    ofSubtype u ∈ Subgroup.centralizer ({τ} : Set (Perm α)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (disjoint_ofSubtype_of_memFixedPoints_self u).commute

theorem fixRestrict_ofSubtype (τ : Perm α) (u : Perm (Function.fixedPoints τ)) :
    fixRestrict τ ⟨ofSubtype u, ofSubtype_mem_centralizer τ u⟩ = u := by
  ext x
  simp [fixRestrict]

theorem fixRestrict_surjective (τ : Perm α) : Function.Surjective (fixRestrict τ) :=
  fun u => ⟨⟨ofSubtype u, ofSubtype_mem_centralizer τ u⟩, fixRestrict_ofSubtype τ u⟩

theorem mem_ker_fixRestrict_iff (τ : Perm α) (g : Subgroup.centralizer ({τ} : Set (Perm α))) :
    g ∈ (fixRestrict τ).ker ↔ ∀ x, τ x = x → (g : Perm α) x = x := by
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, hx⟩)
  · intro h x
    exact Subtype.ext (h x x.2)

end FixRestrict

end CFSG.EvenSporadicStandard.TwoHS.SignS9
