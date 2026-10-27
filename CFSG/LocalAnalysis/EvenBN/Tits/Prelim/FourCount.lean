module

public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup

variable {G : Type*} [Group G]

theorem inv_of_forall_comm_eq_one {K : Subgroup G} (hK : Odd (Nat.card K)) {a : G}
    (ha : orderOf a = 2) (haK : a ∈ normalizer (K : Set G))
    (hfix : ∀ k ∈ K, a * k = k * a → k = 1) {k : G} (hk : k ∈ K) : a * k * a⁻¹ = k⁻¹ := by
  have h := (CFSG.ABGLocalTools.odd_fixed_mul_inverted hK ha haK).1
  have hk' : k ∈ (K : Set G) := hk
  rw [h] at hk'
  obtain ⟨c, hc, i, hi, hci⟩ := Set.mem_mul.1 hk'
  have hc1 : c = 1 :=
    hfix c (mem_inf.1 hc).1 (mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2).symm
  rw [← hci, hc1, one_mul]
  exact hi.2

end CFSG.LocalAnalysis.EvenBN.Tits
