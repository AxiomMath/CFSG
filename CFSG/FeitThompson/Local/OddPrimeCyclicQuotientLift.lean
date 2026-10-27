module

public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {q a : ℕ} {Q : Type*} [Group Q]

theorem mem_of_pow_eq_one_of_lt_of_isCyclic_quotient [Finite Q] (hq : q.Prime)
    (hQ : IsPGroup q Q) {D Q1 : Subgroup Q} [D.Normal] (hD1 : D < Q1)
    (hquot : IsCyclic (Q ⧸ D)) {x : Q} (hx : x ^ q = 1) : x ∈ Q1 := by
  have := Fact.mk hq
  set f := QuotientGroup.mk' D with hf
  have hne : Q1.map f ≠ ⊥ := by
    obtain ⟨y, hyQ1, hyD⟩ := SetLike.exists_of_lt hD1
    intro h
    have hy : f y ∈ Q1.map f := Subgroup.mem_map_of_mem _ hyQ1
    rw [h, Subgroup.mem_bot] at hy
    exact hyD ((QuotientGroup.eq_one_iff y).1 hy)
  have hdvd : q ∣ Nat.card (Q1.map f) := by
    obtain ⟨k, hk⟩ := ((hQ.to_quotient D).to_subgroup (Q1.map f)).exists_card_eq
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by simpa using hk)) hne
    · exact hk ▸ dvd_pow_self q (by omega)
  have hmem : f x ∈ Q1.map f := by
    have hcoe : f x ∈ (Q1.map f : Set (Q ⧸ D)) := by
      rw [coe_eq_setOf_pow_eq_one (Q1.map f)]
      obtain ⟨c, hc⟩ := hdvd
      change (f x) ^ Nat.card (Q1.map f) = 1
      rw [hc, pow_mul, ← map_pow, hx, map_one, one_pow]
    exact hcoe
  have hx' : x ∈ Subgroup.comap f (Q1.map f) := hmem
  rwa [Subgroup.comap_map_eq, hf, QuotientGroup.ker_mk', sup_eq_left.2 hD1.le] at hx'

theorem isCyclic_of_isCyclic_quotient_of_lt_isCyclic [Finite Q] (hq : q.Prime) (hodd : Odd q)
    (hQ : IsPGroup q Q) {D Q1 : Subgroup Q} [D.Normal] (hD1 : D < Q1) (h1 : IsCyclic Q1)
    (hquot : IsCyclic (Q ⧸ D)) : IsCyclic Q := by
  by_contra hnc
  obtain ⟨E, -, -, ⟨g⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hq hodd hQ (⊤ : Subgroup Q)
    (fun _ => hnc (isCyclic_of_surjective (⊤ : Subgroup Q).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩))
  have hEexp : ∀ y : E, (y : Q) ^ q = 1 := fun y =>
    congrArg (Subgroup.subtype E)
      (g.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one]) : y ^ q = 1)
  have hEQ1 : E ≤ Q1 := fun y hy =>
    mem_of_pow_eq_one_of_lt_of_isCyclic_quotient hq hQ hD1 hquot (hEexp ⟨y, hy⟩)
  have hEcyc : IsCyclic E := Subgroup.isCyclic_of_le hEQ1
  have hcard : Nat.card E ∣ q := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (hEexp y)
  rw [Nat.card_congr g.toEquiv, card_pi_multiplicative_zmod] at hcard
  have hle := Nat.le_of_dvd hq.pos hcard
  have hlt : q ^ 1 < q ^ 2 := Nat.pow_lt_pow_right hq.one_lt one_lt_two
  rw [pow_one] at hlt
  exact absurd hle (Nat.not_le.2 hlt)

theorem isCyclic_of_isCyclic_quotient_of_lt_isCyclic_of_card_eq_pow (hq : q.Prime) (hodd : Odd q)
    (hQ : Nat.card Q = q ^ a) {D Q1 : Subgroup Q} [D.Normal] (hD1 : D < Q1) (h1 : IsCyclic Q1)
    (hquot : IsCyclic (Q ⧸ D)) : IsCyclic Q := by
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact pow_ne_zero _ hq.pos.ne')
  exact isCyclic_of_isCyclic_quotient_of_lt_isCyclic hq hodd (IsPGroup.of_card hQ) hD1 h1 hquot

end

end CFSG.FeitThompson
