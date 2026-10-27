module

public import CFSG.ClassicalInvolution.Q3.Q3SBasic

public section

namespace CFSG.ClassicalInvolution.Q3

open Equiv

section Support

variable {n : ℕ}

theorem IsClassicalMember3.eight_le_card_support
    {z : alternatingGroup (Fin n)} {L : Subgroup (alternatingGroup (Fin n))}
    (hL : IsClassicalMember3 L z) : 8 ≤ (z : Perm (Fin n)).support.card := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin n, (z : Perm (Fin n)) a ≠ a := by
    by_contra h
    push Not at h
    exact hL.ne_one (Subtype.ext (Perm.ext h))
  have hS : ¬ 2 ∣ Nat.card (MulAction.stabilizer L a) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer L a) 2 h2
    have hgL : (((g : L) : alternatingGroup (Fin n))) ∈ L := (g : L).2
    have hord : orderOf (((g : L) : alternatingGroup (Fin n))) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hg
    have hgz := hL.eq_of_orderOf_eq_two hgL hord
    have hfix : ((g : L) : L) • a = a := MulAction.mem_stabilizer_iff.mp g.2
    apply ha
    have h1 : ((((g : L) : alternatingGroup (Fin n))) : Perm (Fin n)) a = a := hfix
    rw [hgz] at h1
    exact h1
  have h8 : 8 ∣ Nat.card L := by
    rw [hL.card_eq]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hcard : (MulAction.orbit L a).ncard * Nat.card (MulAction.stabilizer L a) =
      Nat.card L := by
    rw [← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  have hcop : Nat.Coprime 8 (Nat.card (MulAction.stabilizer L a)) := by
    have : Nat.Coprime 2 (Nat.card (MulAction.stabilizer L a)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hS
    simpa using Nat.Coprime.pow_left 3 this
  have h8o : 8 ∣ (MulAction.orbit L a).ncard :=
    hcop.dvd_of_dvd_mul_right (hcard ▸ h8)
  have hpos : 0 < (MulAction.orbit L a).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.mpr ⟨a, MulAction.mem_orbit_self a⟩
  have h8le : 8 ≤ (MulAction.orbit L a).ncard := Nat.le_of_dvd hpos h8o
  have hsub : (MulAction.orbit L a : Set (Fin n)) ⊆ ((z : Perm (Fin n)).support : Set (Fin n)) := by
    rintro _ ⟨l, rfl⟩
    have hcomm := hL.mul_eq (x := ((l : L) : alternatingGroup (Fin n))) l.2
    have hc : ∀ x : Fin n, ((l : alternatingGroup (Fin n)) : Perm (Fin n)) ((z : Perm (Fin n)) x) =
        (z : Perm (Fin n)) (((l : alternatingGroup (Fin n)) : Perm (Fin n)) x) := fun x =>
      congrArg (fun p : alternatingGroup (Fin n) => (p : Perm (Fin n)) x) hcomm
    simp only [Finset.mem_coe, Perm.mem_support]
    intro h
    apply ha
    have h' : (z : Perm (Fin n)) (((l : alternatingGroup (Fin n)) : Perm (Fin n)) a) =
        ((l : alternatingGroup (Fin n)) : Perm (Fin n)) a := h
    rw [← hc a] at h'
    exact ((l : alternatingGroup (Fin n)) : Perm (Fin n)).injective h'
  calc 8 ≤ (MulAction.orbit L a).ncard := h8le
    _ ≤ ((z : Perm (Fin n)).support : Set (Fin n)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (z : Perm (Fin n)).support.card := Set.ncard_coe_finset _

end Support

section CycleType

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_eq_replicate_two {σ : Perm α} (h2 : orderOf σ = 2) :
    ∃ m : ℕ, σ.cycleType = Multiset.replicate m 2 ∧ σ.support.card = 2 * m := by
  have hp : (orderOf σ).Prime := by rw [h2]; exact Nat.prime_two
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order hp
  rw [h2] at hk
  refine ⟨k + 1, hk, ?_⟩
  rw [← Perm.sum_cycleType, hk, Multiset.sum_replicate]
  simp [mul_comm]

theorem even_of_sign_eq_one {σ : Perm α} (h2 : orderOf σ = 2) (hs : Perm.sign σ = 1) :
    ∃ m : ℕ, σ.cycleType = Multiset.replicate (2 * m) 2 ∧ σ.support.card = 4 * m := by
  obtain ⟨m, hm, hc⟩ := cycleType_eq_replicate_two h2
  rw [Perm.sign_of_cycleType, hm, Multiset.sum_replicate, Multiset.card_replicate] at hs
  have hs' : (-1 : ℤˣ) ^ (m • 2 + m) = 1 := hs
  have heven : Even (m • 2 + m) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hs'
    exact absurd hs' (by decide)
  have hm2 : Even m := by
    simp only [smul_eq_mul] at heven
    have : m * 2 + m = 3 * m := by ring
    rw [this] at heven
    rcases Nat.even_mul.mp heven with h | h
    · exact absurd h (by decide)
    · exact h
  obtain ⟨k, hk⟩ := hm2
  refine ⟨k, ?_, ?_⟩
  · rw [hm, hk]; congr 1; ring
  · rw [hc, hk]; ring

end CycleType

end CFSG.ClassicalInvolution.Q3
