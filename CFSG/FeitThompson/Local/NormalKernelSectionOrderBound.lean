module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

variable {L : Type*} [Group L] {H E K N : Subgroup L}

theorem natCard_quotient_subgroupOf_eq_relIndex :
    Nat.card (↥K ⧸ N.subgroupOf K) = N.relIndex K :=
  (Subgroup.index_eq_card _).symm

theorem one_lt_relIndex_of_lt [Finite (↥K ⧸ N.subgroupOf K)] (h : N < K) : 1 < N.relIndex K := by
  rw [← natCard_quotient_subgroupOf_eq_relIndex, ← Subgroup.index_eq_card]
  exact Subgroup.one_lt_index_of_ne_top
    (fun hc => absurd (Subgroup.subgroupOf_eq_top.1 hc) h.not_ge)

theorem odd_relIndex (hL : Odd (Nat.card L)) (K N : Subgroup L) : Odd (N.relIndex K) := by
  rw [← natCard_quotient_subgroupOf_eq_relIndex]
  exact odd_natCard_quotient _ (odd_natCard_subgroup hL K)

private theorem two_mul_dvd_sub_one_of_odd {e m : ℕ} (he : Odd e) (hm : Odd m)
    (hdvd : e ∣ m - 1) : 2 * e ∣ m - 1 := by
  obtain ⟨k, hk⟩ := hdvd
  have hev : Even (m - 1) := Nat.Odd.sub_odd hm odd_one
  rw [hk] at hev
  rcases Nat.even_mul.1 hev with h | h
  · exact absurd h (Nat.not_even_iff_odd.2 he)
  · obtain ⟨j, hj⟩ := h
    exact ⟨j, by rw [hk, hj]; ring⟩

theorem natCard_dvd_relIndex_sub_one [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hKH : K ≤ H)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) :
    Nat.card ↥E ∣ N.relIndex K - 1 := by
  have h := card_dvd_card_sub_one_of_fixedPointFree
    (φ := (factorConj K N).comp E.subtype) (fun u hu =>
      fixedPointFree_factorConj (E := E) hKH hC u.2 (fun hu1 => hu (Subtype.ext hu1)))
  rwa [natCard_quotient_subgroupOf_eq_relIndex] at h

theorem two_mul_natCard_dvd_relIndex_sub_one [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hL : Odd (Nat.card L)) (hKH : K ≤ H)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) :
    2 * Nat.card ↥E ∣ N.relIndex K - 1 :=
  two_mul_dvd_sub_one_of_odd (odd_natCard_subgroup hL E) (odd_relIndex hL K N)
    (natCard_dvd_relIndex_sub_one hKH hC)

theorem two_mul_index_dvd_relIndex_sub_one [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hL : Odd (Nat.card L)) (hHE : H.IsComplement' E) (hKH : K ≤ H)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) :
    2 * H.index ∣ N.relIndex K - 1 := by
  rw [index_eq_natCard_of_isComplement' hHE]
  exact two_mul_natCard_dvd_relIndex_sub_one (H := H) (E := E) hL hKH hC

theorem relIndex_sub_one_pos [Finite L] (hNK : N < K) : 0 < N.relIndex K - 1 := by
  have := one_lt_relIndex_of_lt (K := K) (N := N) hNK
  omega

theorem two_mul_natCard_add_one_le_relIndex [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hL : Odd (Nat.card L)) (hNK : N < K) (hKH : K ≤ H)
    (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) :
    2 * Nat.card ↥E + 1 ≤ N.relIndex K := by
  have h1 : 1 < N.relIndex K := one_lt_relIndex_of_lt hNK
  have h2 : 2 * Nat.card ↥E ∣ N.relIndex K - 1 :=
    two_mul_natCard_dvd_relIndex_sub_one (H := H) (E := E) hL hKH hC
  have h3 := Nat.le_of_dvd (by omega) h2
  omega

theorem two_mul_index_add_one_le_relIndex [Finite L] [H.Normal] [K.Normal] [N.Normal]
    [Group.IsNilpotent ↥H] (hL : Odd (Nat.card L)) (hHE : H.IsComplement' E) (hNK : N < K)
    (hKH : K ≤ H) (hC : ∀ v ∈ E, v ≠ 1 → H ⊓ Subgroup.centralizer {v} = ⊥) :
    2 * H.index + 1 ≤ N.relIndex K := by
  rw [index_eq_natCard_of_isComplement' hHE]
  exact two_mul_natCard_add_one_le_relIndex (H := H) (E := E) hL hNK hKH hC

end CFSG.FeitThompson
