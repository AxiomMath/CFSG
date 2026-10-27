module

public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

theorem isCyclic_units_of_finite_field (K : Type*) [Field K] [Finite K] : IsCyclic Kˣ :=
  inferInstance

theorem exists_ne_zero_forall_exists_pow_eq (K : Type*) [Field K] [Finite K] :
    ∃ g : K, g ≠ 0 ∧ ∀ x : K, x ≠ 0 → ∃ n : ℕ, g ^ n = x := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  refine ⟨(u : K), u.ne_zero, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hu (Units.mk0 x hx)
  exact ⟨n, by simpa using congrArg Units.val hn⟩

theorem exists_zpowers_units_eq_top (K : Type*) [Field K] [Finite K] :
    ∃ g : Kˣ, Subgroup.zpowers g = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, by simpa [Subgroup.eq_top_iff'] using hg⟩

theorem exists_orderOf_units_eq_card_sub_one (K : Type*) [Field K] [Finite K] :
    ∃ g : Kˣ, orderOf g = Nat.card K - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, by rw [← Nat.card_units (α := K), orderOf_eq_card_of_forall_mem_zpowers hg]⟩

end

end CFSG.FeitThompson
