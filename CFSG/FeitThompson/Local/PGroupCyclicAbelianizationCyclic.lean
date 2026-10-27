module

public import Mathlib.GroupTheory.Frattini
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p a : ℕ} {P : Type*} [Group P]

theorem exists_zpowers_sup_eq_top_of_isCyclic_quotient {N : Subgroup P} [N.Normal]
    [IsCyclic (P ⧸ N)] : ∃ x : P, zpowers x ⊔ N = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P ⧸ N)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨x, top_le_iff.1 fun y _ => ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg (QuotientGroup.mk y))
  have hmem : (x ^ k)⁻¹ * y ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_zpow, hk]
    simp
  have hy : y = x ^ k * ((x ^ k)⁻¹ * y) := by group
  rw [hy]
  exact mul_mem (mem_sup_left (mem_zpowers_iff.2 ⟨k, rfl⟩)) (mem_sup_right hmem)

theorem isCyclic_of_natCard_eq_prime_pow_of_isCyclic_quotient_commutator
    (hp : p.Prime) (hP : Nat.card P = p ^ a) [IsCyclic (P ⧸ commutator P)] : IsCyclic P := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨x, hx⟩ := exists_zpowers_sup_eq_top_of_isCyclic_quotient (N := commutator P)
  have hsup : zpowers x ⊔ frattini P = ⊤ := by
    rw [eq_top_iff, ← hx]
    exact sup_le le_sup_left (le_sup_right.trans' (commutator_le_frattini (n := a) hp hP))
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨x, frattini_nongenerating hsup⟩

theorem isCyclic_of_natCard_eq_prime_pow_of_isCyclic_abelianization
    (hp : p.Prime) (hP : Nat.card P = p ^ a) [hc : IsCyclic (Abelianization P)] : IsCyclic P :=
  have : IsCyclic (P ⧸ commutator P) := hc
  isCyclic_of_natCard_eq_prime_pow_of_isCyclic_quotient_commutator hp hP

theorem isCyclic_of_isPGroup_of_isCyclic_quotient_commutator [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) [IsCyclic (P ⧸ commutator P)] : IsCyclic P := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact isCyclic_of_natCard_eq_prime_pow_of_isCyclic_quotient_commutator (a := n) hp hn

end

end CFSG.FeitThompson
