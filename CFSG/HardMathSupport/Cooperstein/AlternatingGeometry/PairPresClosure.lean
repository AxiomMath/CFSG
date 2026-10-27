module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairPreserving

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}

theorem mem_closure_blockSwaps_of_fix (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (a : Ω)
    {h : Perm Ω} (hh : h ∈ pairPres σ hσ1 hσ2) (ha : h a = a) :
    h ∈ Subgroup.closure {t : Perm Ω | ∃ y, y ≠ a ∧ y ≠ σ a ∧ t = swap y (σ y)} := by
  suffices H : ∀ n : ℕ, ∀ h : Perm Ω, h.support.card = n → h ∈ pairPres σ hσ1 hσ2 → h a = a →
      h ∈ Subgroup.closure {t : Perm Ω | ∃ y, y ≠ a ∧ y ≠ σ a ∧ t = swap y (σ y)} from
    H _ h rfl hh ha
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn hh ha
    by_cases h1 : h = 1
    · rw [h1]; exact one_mem _
    obtain ⟨y, hy⟩ : ∃ y, h y ≠ y := by
      by_contra hno
      push Not at hno
      exact h1 (Equiv.ext hno)
    have hhy : ∀ z, h z = z ∨ h z = σ z := hh
    have hya : y ≠ a := fun e => hy (e ▸ ha)
    have hσa : h (σ a) = σ a := by
      rcases pair_cases hσ1 hσ2 hhy a with ⟨-, e⟩ | ⟨e, -⟩
      · exact e
      · exact absurd (e.symm.trans ha) (hσ1 a)
    have hyσa : y ≠ σ a := fun e => hy (e ▸ hσa)
    have hhy' : h y = σ y := (hhy y).resolve_left hy
    have hhσy : h (σ y) = y := by
      rcases pair_cases hσ1 hσ2 hhy y with ⟨e, -⟩ | ⟨-, e⟩
      · exact absurd e hy
      · exact e
    have hty : swap y (σ y) ∈ Subgroup.closure {t : Perm Ω | ∃ y, y ≠ a ∧ y ≠ σ a ∧ t = swap y (σ y)} :=
      Subgroup.subset_closure ⟨y, hya, hyσa, rfl⟩
    have hmem : swap y (σ y) * h ∈ pairPres σ hσ1 hσ2 :=
      (pairPres σ hσ1 hσ2).mul_mem (swap_mem_pairPres hσ1 hσ2 y) hh
    have hay : a ≠ σ y := fun e => hyσa (by rw [e, hσ2])
    have hfix : (swap y (σ y) * h) a = a := by
      rw [Perm.mul_apply, ha, swap_apply_of_ne_of_ne hya.symm hay]
    have hlt : (swap y (σ y) * h).support.card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨?_, ?_⟩
      · intro z hz
        rw [Equiv.Perm.mem_support] at hz ⊢
        intro hzz
        apply hz
        rw [Perm.mul_apply, hzz]
        have hzy : z ≠ y := fun e => hy (e ▸ hzz)
        have hzσy : z ≠ σ y := fun e => by
          rw [e] at hzz
          have : h (σ y) = y := hhσy
          rw [this] at hzz
          exact hσ1 y hzz.symm
        exact swap_apply_of_ne_of_ne hzy hzσy
      · intro hsub
        have := hsub (Equiv.Perm.mem_support.2 hy)
        rw [Equiv.Perm.mem_support, Perm.mul_apply, hhy', swap_apply_right] at this
        exact this rfl
    have := ih _ hlt (swap y (σ y) * h) rfl hmem hfix
    have hheq : h = swap y (σ y) * (swap y (σ y) * h) := by
      rw [← mul_assoc, swap_mul_self, one_mul]
    rw [hheq]
    exact Subgroup.mul_mem _ hty this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
