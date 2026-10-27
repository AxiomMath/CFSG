module

public import CFSG.LieType.SteinbergBRSmallAltSylow

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Equiv Equiv.Perm CFSG.LieType.SteinbergBR.SmallAlt

theorem exists_even_conj_of_card_support_eq {α : Type*} [Fintype α] [DecidableEq α] {σ σ' : Perm α}
    (hσ : σ * σ = 1) (hσ' : σ' * σ' = 1) (h : σ.support.card = σ'.support.card) :
    ∃ g : Perm α, sign g = 1 ∧ g * σ * g⁻¹ = σ' := by
  by_cases h0 : σ = 1
  · have h1 : σ'.support.card = 0 := by rw [← h, h0]; simp
    have h2 : σ' = 1 := Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 h1)
    exact ⟨1, by simp, by rw [h0, h2]; simp⟩
  · have h2 : σ' ≠ 1 := by
      intro h2
      apply h0
      have : σ.support.card = 0 := by rw [h, h2]; simp
      exact Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 this)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ho : orderOf σ = 2 := orderOf_eq_prime (by rwa [sq]) h0
    have ho' : orderOf σ' = 2 := orderOf_eq_prime (by rwa [sq]) h2
    obtain ⟨m, hm⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
    obtain ⟨m', hm'⟩ := Perm.cycleType_prime_order (σ := σ') (by rw [ho']; exact Nat.prime_two)
    rw [ho] at hm
    rw [ho'] at hm'
    have hs : σ.cycleType.sum = σ.support.card := Perm.sum_cycleType σ
    have hs' : σ'.cycleType.sum = σ'.support.card := Perm.sum_cycleType σ'
    rw [hm, Multiset.sum_replicate] at hs
    rw [hm', Multiset.sum_replicate] at hs'
    have hmm : m = m' := by simp at hs hs'; omega
    have hct : σ.cycleType = σ'.cycleType := by rw [hm, hm', hmm]
    obtain ⟨g, hg⟩ := isConj_iff.1 (Perm.isConj_iff_cycleType_eq.2 hct)
    rcases Int.units_eq_one_or (sign g) with h1 | h1
    · exact ⟨g, h1, hg⟩
    · have : ∃ x, σ x ≠ x := by
        by_contra hcon
        push Not at hcon
        exact h0 (Equiv.ext hcon)
      obtain ⟨x, hx⟩ := this
      have hσσ : σ (σ x) = x := by
        have := congrArg (fun f : Perm α => f x) hσ
        simpa using this
      have hc : σ * swap x (σ x) = swap x (σ x) * σ := by
        rw [mul_swap_eq_swap_mul, hσσ, Equiv.swap_comm]
      refine ⟨g * swap x (σ x), ?_, ?_⟩
      · rw [map_mul, h1, sign_swap hx.symm]
        decide
      · calc g * swap x (σ x) * σ * (g * swap x (σ x))⁻¹
            = g * (swap x (σ x) * σ * (swap x (σ x))⁻¹) * g⁻¹ := by group
          _ = g * σ * g⁻¹ := by rw [← hc]; group
          _ = σ' := hg

theorem card_support_eq_four_of_even {σ : Perm (Fin 7)} (hσ : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : sign σ = 1) : σ.support.card = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf σ = 2 := orderOf_eq_prime (by rwa [sq]) h1
  obtain ⟨m, hm⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hm
  have hsum : σ.cycleType.sum = σ.support.card := Perm.sum_cycleType σ
  have hle : σ.support.card ≤ 7 := by
    have := Finset.card_le_univ σ.support
    simpa using this
  rw [hm, Multiset.sum_replicate] at hsum
  have hsign := Perm.sign_of_cycleType σ
  rw [hm, Multiset.sum_replicate, Multiset.card_replicate, hs] at hsign
  simp only [smul_eq_mul] at hsum
  have hm3 : m ≤ 2 := by omega
  interval_cases m
  · exfalso
    revert hsign
    decide
  · omega
  · exfalso
    revert hsign
    decide

theorem cent_a7P (τ : Perm (Fin 7)) (hτ : ∀ i : Fin 8, τ * a7P i = a7P i * τ) :
    τ = 1 ∨ τ = a7P 1 ∨ τ = swap 5 6 ∨ τ = a7P 1 * swap 5 6 := by
  have hcheck6 : ∀ e : Equiv.Perm (Fin 6),
      (∀ i : Fin 8, Equiv.Perm.decomposeFin.symm (0, e) * a7P i =
        a7P i * Equiv.Perm.decomposeFin.symm (0, e)) →
      Equiv.Perm.decomposeFin.symm (0, e) = 1 ∨ Equiv.Perm.decomposeFin.symm (0, e) = a7P 1 ∨
        Equiv.Perm.decomposeFin.symm (0, e) = swap 5 6 ∨
        Equiv.Perm.decomposeFin.symm (0, e) = a7P 1 * swap 5 6 := by
    decide +kernel
  have hτ0 : τ 0 = 0 := by
    have h4 := congrArg (fun f : Equiv.Perm (Fin 7) => f 0) (hτ 4)
    simp only [Equiv.Perm.mul_apply] at h4
    rw [a7P_fix_zero 4] at h4
    exact a7P_four_fix _ h4.symm
  obtain ⟨e, he⟩ : ∃ e : Equiv.Perm (Fin 6), τ = Equiv.Perm.decomposeFin.symm (0, e) := by
    refine ⟨(Equiv.Perm.decomposeFin τ).2, ?_⟩
    set d := Equiv.Perm.decomposeFin τ with hd
    have hd1 : d.1 = 0 := by
      have : Equiv.Perm.decomposeFin.symm d 0 = d.1 := by
        rw [show d = (d.1, d.2) from rfl, Equiv.Perm.decomposeFin_symm_apply_zero]
      rw [← this, hd, Equiv.symm_apply_apply, hτ0]
    rw [← hd1, show (d.1, d.2) = d from rfl, hd, Equiv.symm_apply_apply]
  rw [he] at hτ ⊢
  exact hcheck6 e hτ

theorem a7P_central_idx : ∀ i : Fin 8, (∀ j : Fin 8, a7P i * a7P j = a7P j * a7P i) →
    i = 0 ∨ i = 1 := by
  decide

theorem a7P_invol_idx : ∀ i : Fin 8, a7P i * a7P i = 1 →
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7 := by
  decide

theorem a7P_pair : a7P 1 * a7P 2 = a7P 3 ∧ a7P 1 * a7P 3 = a7P 2 ∧ a7P 1 * a7P 6 = a7P 7 ∧
    a7P 1 * a7P 7 = a7P 6 := by
  decide

theorem a7P_dichotomy {i j : Fin 8} (hi : i = 2 ∨ i = 3) (hj : j = 6 ∨ j = 7) {τ : Perm (Fin 7)}
    (hτ : τ = swap 5 6 ∨ τ = a7P 1 * swap 5 6) :
    (a7P i * τ).support.card = τ.support.card ∨ (a7P j * τ).support.card = τ.support.card := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hτ with rfl | rfl <;> decide

theorem a7P_rho {i : Fin 8} (hi : i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7) :
    ∃ ρ : Perm (Fin 7), sign ρ = 1 ∧ ρ * a7P 1 * ρ⁻¹ = a7P i ∧
      ρ * a7P i * ρ⁻¹ = a7P 1 * a7P i := by
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨swap 1 2 * swap 2 3, by decide, by decide, by decide⟩
  · exact ⟨swap 2 3 * swap 1 2, by decide, by decide, by decide⟩
  · exact ⟨(swap 2 5 * swap 1 2) * (swap 4 6 * swap 3 4), by decide, by decide, by decide⟩
  · exact ⟨(swap 1 2 * swap 2 5) * (swap 3 4 * swap 4 6), by decide, by decide, by decide⟩

theorem sign_a7P (i : Fin 8) : sign (a7P i) = 1 := a7P_sign i

end CFSG.GH74.GLS.Th2.P43f
