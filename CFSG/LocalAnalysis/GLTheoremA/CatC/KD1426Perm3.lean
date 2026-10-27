module

public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.GCD

public section

open Equiv

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Perm3

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem mem_support_apply' {σ : Perm α} {x : α} (hx : x ∈ σ.support) : σ x ∈ σ.support := by
  rw [Equiv.Perm.mem_support] at hx ⊢
  intro h
  exact hx (σ.injective (by simpa using h))

theorem three_cycle_orbit {σ : Perm α} (h3 : σ ^ 3 = 1) (hcard : (σ.support).card = 3) {p : α}
    (hp : p ∈ σ.support) : ∀ t ∈ σ.support, ∃ i : ℕ, i < 3 ∧ (σ ^ i) p = t := by
  have hp1 : σ p ≠ p := Equiv.Perm.mem_support.1 hp
  have hσ3 : σ (σ (σ p)) = p := by
    have := congrArg (fun π : Perm α => π p) h3
    simpa [pow_succ, Perm.mul_apply] using this
  have hp2 : σ (σ p) ≠ σ p := fun h => hp1 (σ.injective h)
  have hne2 : σ (σ p) ≠ p := fun h => hp1 (by
    have h' : σ (σ (σ p)) = σ p := by rw [h]
    rw [hσ3] at h'
    exact h'.symm)
  have hsub : ({p, σ p, σ (σ p)} : Finset α) ⊆ σ.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact mem_support_apply' hp
    · exact mem_support_apply' (mem_support_apply' hp)
  have hcard3 : ({p, σ p, σ (σ p)} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hp2.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp1.symm, hne2.symm⟩
  have heq : ({p, σ p, σ (σ p)} : Finset α) = σ.support :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hcard])
  intro t ht
  rw [← heq] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩

theorem centralizer_eq_pow_on_support {σ x : Perm α} (h3 : σ ^ 3 = 1) (hcard : (σ.support).card = 3)
    (hx : x * σ = σ * x) : ∃ i : ℕ, i < 3 ∧ ∀ t ∈ σ.support, x t = (σ ^ i) t := by
  have hcomm : ∀ t, x (σ t) = σ (x t) := fun t => by
    have := congrArg (fun π : Perm α => π t) hx
    simpa [Perm.mul_apply] using this
  have hstable : ∀ t ∈ σ.support, x t ∈ σ.support := by
    intro t ht
    rw [Equiv.Perm.mem_support] at ht ⊢
    intro h
    apply ht
    apply x.injective
    rw [hcomm t, h]
  have hne : σ.support.Nonempty := by
    rw [← Finset.card_pos, hcard]
    norm_num
  obtain ⟨p, hp⟩ := hne
  obtain ⟨i, hi3, hxp⟩ := three_cycle_orbit h3 hcard hp (x p) (hstable p hp)
  refine ⟨i, hi3, ?_⟩
  have hpow : ∀ k : ℕ, x ((σ ^ k) p) = (σ ^ k) (x p) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, Perm.mul_apply, hcomm, ih]
  intro t ht
  obtain ⟨k, _, rfl⟩ := three_cycle_orbit h3 hcard hp t ht
  rw [hpow k, ← hxp]
  have hc : σ ^ k * σ ^ i = σ ^ i * σ ^ k := (Commute.refl σ).pow_pow k i
  have := congrArg (fun π : Perm α => π p) hc
  simpa [Perm.mul_apply] using this

end CFSG.LocalAnalysis.GLTheoremA.KD1426Perm3

end
