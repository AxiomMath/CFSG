module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedPrimeLayer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

theorem quasisimple_fixed_layer_full_under_trivial_core_action {A X : Type*} [Group A] [Group X]
    [Finite A] [Finite X] (p : ℕ) [Fact p.Prime] (hX : IsQuasisimple X) (hA : IsPGroup p A)
    (α : A →* MulAut X) (hQ : IsQuasisimple (X ⧸ pPrimeCore p X))
    (htriv : ∀ (a : A) (x : X), ((α a x : X) : X ⧸ pPrimeCore p X) = (x : X ⧸ pPrimeCore p X))
    (C : Subgroup X) (hC : ∀ x : X, x ∈ C ↔ ∀ a : A, α a x = x) :
    (∀ (a : A) (x : X), α a x = x) ∧ (pLayer C p).map C.subtype = ⊤ := by
  set N := pPrimeCore p X with hNdef
  set T := (pLayer C p).map C.subtype with hT
  obtain ⟨hTN, -, -⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.fixed_prime_layer_covers_core_quotient p hA α hQ
      htriv C hC T hT
  have hNc : N ≤ center X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hX (inferInstance : N.Normal) with h | h
    · exfalso
      have := CFSG.LocalCores.isQuasisimple_nontrivial hQ
      obtain ⟨u, v, huv⟩ := exists_pair_ne (X ⧸ N)
      induction u using QuotientGroup.induction_on with | H x => ?_
      induction v using QuotientGroup.induction_on with | H y => ?_
      exact huv (QuotientGroup.eq.2 (by rw [h]; trivial))
    · exact h
  have hcomm : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro g _ g' _
    have hdec : ∀ y : X, ∃ t ∈ T, ∃ n ∈ N, t * n = y := fun y => by
      have hy : y ∈ ((T ⊔ N : Subgroup X) : Set X) := by rw [hTN]; trivial
      rw [Subgroup.mul_normal] at hy
      obtain ⟨t, ht, n, hn, rfl⟩ := hy
      exact ⟨t, ht, n, hn, rfl⟩
    obtain ⟨t, ht, n, hn, rfl⟩ := hdec g
    obtain ⟨t', ht', n', hn', rfl⟩ := hdec g'
    have hn1 := Subgroup.mem_center_iff.1 (hNc hn)
    have hn2 := Subgroup.mem_center_iff.1 (hNc hn')
    have hc : ⁅t * n, t' * n'⁆ = ⁅t, t'⁆ := by
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
      calc t * n * (t' * n') * (n⁻¹ * t⁻¹) * (n'⁻¹ * t'⁻¹)
          = t * (n * t') * (n' * n⁻¹) * t⁻¹ * n'⁻¹ * t'⁻¹ := by group
        _ = t * (t' * n) * (n⁻¹ * n') * t⁻¹ * n'⁻¹ * t'⁻¹ := by
          rw [← hn1 t', show n' * n⁻¹ = n⁻¹ * n' from Subgroup.mem_center_iff.1
            (Subgroup.inv_mem _ (hNc hn)) n']
        _ = t * t' * (n' * t⁻¹) * n'⁻¹ * t'⁻¹ := by group
        _ = t * t' * (t⁻¹ * n') * n'⁻¹ * t'⁻¹ := by rw [← hn2 t⁻¹]
        _ = t * t' * t⁻¹ * t'⁻¹ := by group
    rw [hc, commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem ht ht') (T.inv_mem ht)) (T.inv_mem ht')
  have hTtop : T = ⊤ := by
    have hperf := hX.1
    rw [Group.isPerfect_def] at hperf
    exact eq_top_iff.2 (hperf ▸ hcomm)
  have hCtop : C = ⊤ := eq_top_iff.2 fun x _ => by
    obtain ⟨y, -, rfl⟩ : x ∈ T := by rw [hTtop]; trivial
    exact y.2
  refine ⟨fun a x => (hC x).1 (by rw [hCtop]; trivial) a, hTtop⟩

end CFSG.LocalAnalysis.ComponentInitial
