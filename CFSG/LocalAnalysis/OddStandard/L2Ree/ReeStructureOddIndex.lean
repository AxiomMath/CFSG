module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup

variable {G : Type*} [Group G] {L M P : Subgroup G}

theorem le_of_isPGroup_of_odd_relIndex (hN : (L.subgroupOf M).Normal) (hodd : Odd (L.relIndex M))
    (hPM : P ≤ M) (hP : IsPGroup 2 P) : P ≤ L := by
  intro x hx
  have hxM : x ∈ M := hPM hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hxk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hxk : (⟨x, hxM⟩ : ↥M) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxk')
  set q := QuotientGroup.mk' (L.subgroupOf M) ⟨x, hxM⟩ with hq
  have hq2 : q ^ (2 ^ k) = 1 := by rw [hq, ← map_pow, hxk, map_one]
  have hqodd : Odd (orderOf q) := by
    refine hodd.of_dvd_nat ?_
    have hcard : Nat.card (↥M ⧸ L.subgroupOf M) = L.relIndex M := by
      rw [← Subgroup.index_eq_card]
      rfl
    rw [← hcard]
    exact orderOf_dvd_natCard q
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hq2)
  have hj0 : j = 0 := by
    by_contra hne
    have hev : Even (orderOf q) := by rw [hj]; exact Nat.even_pow.2 ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.2 hqodd) hev
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have hxN : (⟨x, hxM⟩ : ↥M) ∈ L.subgroupOf M :=
    (QuotientGroup.eq_one_iff (N := L.subgroupOf M) ⟨x, hxM⟩).1 hj
  exact hxN

theorem exists_conj_le_of_odd_relIndex {E : Subgroup G} (hLM : L ≤ M) (hN : (L.subgroupOf M).Normal)
    (hodd : Odd (L.relIndex M))
    (hsyl : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P →
      ∃ g ∈ L, P ≤ E.map (MulAut.conj g).toMonoidHom) :
    ∀ P : Subgroup G, P ≤ M → IsPGroup 2 P →
      ∃ g ∈ M, P ≤ E.map (MulAut.conj g).toMonoidHom := by
  intro P hPM hP
  obtain ⟨g, hg, hPg⟩ := hsyl P (le_of_isPGroup_of_odd_relIndex hN hodd hPM hP) hP
  exact ⟨g, hLM hg, hPg⟩

end CFSG.OddStandard.L2Ree
