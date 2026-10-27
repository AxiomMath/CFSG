module

public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.Generic.S45.LLift
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.Centralizer
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 Subgroup CFSG.GH74.Generic.S45
open scoped commutatorElement

theorem exists_involution_mem_of_quasisimple {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsQuasisimple ↥L) : ∃ e ∈ L, e * e = 1 ∧ e ≠ 1 := by
  obtain ⟨P, hP, hP4⟩ := exists_two_subgroup_card_ge_four hL
  have h2 : 2 ∣ Nat.card ↥L := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, pow_zero] at hk; omega
      · exact h
    have : 2 ∣ Nat.card P := by rw [hk]; exact dvd_pow_self 2 (by omega)
    exact this.trans (Subgroup.card_subgroup_dvd_card P)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2
  have ht2 : t * t = 1 := by
    have : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rwa [pow_two] at this
  refine ⟨(t : G), t.2, congrArg Subtype.val ht2, ?_⟩
  intro h1
  have : t = 1 := Subtype.ext h1
  rw [this, orderOf_one] at ht
  omega

end CFSG.GH74.Generic
