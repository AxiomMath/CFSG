module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.PGroupCyclicAbelianizationCyclic
import CFSG.FeitThompson.Local.NilpotentFrobeniusAbelianizationPrimePower
import CFSG.FeitThompson.Local.NilpotentAbelianizationSamePrimes
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {L : Type*} [Group L] {H E : Subgroup L} {p e : ℕ}

theorem two_mul_add_one_le_of_odd_of_dvd_sub_one (hp : Odd p) (he : Odd e) (hp3 : 3 ≤ p)
    (hep : e ∣ p - 1) : 2 * e + 1 ≤ p := by
  obtain ⟨k, hk⟩ := hep
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hkeven : Even k := by
    rw [← Nat.not_odd_iff_even]
    intro hko
    obtain ⟨m, hm⟩ := hp
    obtain ⟨n, hn⟩ := he.mul hko
    omega
  obtain ⟨j, hj⟩ := hkeven
  have hk2 : 2 ≤ k := by omega
  calc 2 * e + 1 ≤ e * k + 1 := by nlinarith
    _ = p := by omega

section Main

variable [Finite L] [H.Normal] [Group.IsNilpotent ↥H]
  (hL : Odd (Nat.card L)) (hH : H ≠ ⊥)
  (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥)
  (hp : p.Prime) (hpH : p ∣ Nat.card ↥H)

include hL hH hC hp hpH

theorem isCyclic_of_relIndex_commutator_self_le_of_prime_dvd
    (hbd : (⁅H, H⁆).relIndex H ≤ 4 * Nat.card ↥E ^ 2 + 1) (hep : Nat.card ↥E ∣ p - 1) :
    IsCyclic ↥H := by
  obtain ⟨q, a, d, hq, ha, hd, hcard, hidx⟩ :=
    exists_prime_natCard_eq_pow_relIndex_commutator_self_eq_pow (E := E) hL hH hC hbd
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow (hcard ▸ hpH))
  subst hpq
  have hpodd : Odd p := hL.of_dvd_nat (hpH.trans H.card_subgroup_dvd_card)
  have heodd : Odd (Nat.card ↥E) := hL.of_dvd_nat E.card_subgroup_dvd_card
  have hp3 : 3 ≤ p := by
    obtain ⟨m, hm⟩ := hpodd
    have := hp.two_le
    omega
  have hple : 2 * Nat.card ↥E + 1 ≤ p :=
    two_mul_add_one_le_of_odd_of_dvd_sub_one hpodd heodd hp3 hep
  have hlt : p ^ d < p ^ 2 :=
    calc p ^ d = (⁅H, H⁆).relIndex H := hidx.symm
      _ ≤ 4 * Nat.card ↥E ^ 2 + 1 := hbd
      _ < (2 * Nat.card ↥E + 1) ^ 2 := by nlinarith [Nat.card_pos (α := ↥E)]
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hple 2
  have hd1 : d = 1 := by
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).1 hlt
    omega
  subst hd1
  have hfact : Fact p.Prime := ⟨hp⟩
  have habcard : Nat.card (Abelianization ↥H) = p := by
    rw [natCard_abelianization_eq_index_commutator,
      ← relIndex_commutator_self_eq_index_commutator, hidx, pow_one]
  have : IsCyclic (Abelianization ↥H) := isCyclic_of_prime_card habcard
  exact isCyclic_of_natCard_eq_prime_pow_of_isCyclic_abelianization hq hcard

theorem isCyclic_of_relIndex_commutator_self_le_of_prime_dvd_of_isComplement'
    (hHE : H.IsComplement' E) (hbd : (⁅H, H⁆).relIndex H ≤ 4 * H.index ^ 2 + 1)
    (hep : H.index ∣ p - 1) : IsCyclic ↥H := by
  rw [index_eq_natCard_of_isComplement' hHE] at hbd hep
  exact isCyclic_of_relIndex_commutator_self_le_of_prime_dvd (E := E) hL hH hC hp hpH hbd hep

end Main

end CFSG.FeitThompson

end
