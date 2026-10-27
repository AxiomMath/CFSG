module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KC.OrbRow

open Subgroup

variable {α ι : Type*} [Finite α]

@[expose] def tupStab (E : Finset (ι → α)) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ e ∈ E, (fun i => g (e i)) ∈ E}
  one_mem' e he := he
  mul_mem' {g h} hg hh e he := hg _ (hh e he)
  inv_mem' {g} hg e he := by
    have hpow : ∀ k : ℕ, ∀ e ∈ E, (fun i => (g ^ k) (e i)) ∈ E := by
      intro k
      induction k with
      | zero => intro e he; simpa using he
      | succ k ih =>
        intro e he
        have := hg _ (ih e he)
        simpa [pow_succ', Equiv.Perm.mul_apply] using this
    have h1 : g ^ (orderOf g - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact hpow _ e he

theorem key_orbit {K R : Subgroup (Equiv.Perm α)} {Rg : Set (Equiv.Perm α)} (hR : R = closure Rg)
    (hRK : R ≤ K) (v : ι → α) (hv : ∀ g ∈ K, (∀ i, g (v i) = v i) → g = 1) (E : Finset (ι → α))
    (hroot : v ∈ E) (hclos : ∀ e ∈ E, ∀ r ∈ Rg, (fun i => r (e i)) ∈ E)
    (hreach : ∀ e ∈ E, ∃ r ∈ R, (fun i => r (v i)) = e) :
    Nat.card R = E.card ∧ ∀ y ∈ K, (fun i => y (v i)) ∈ E → y ∈ R := by
  have hRS : R ≤ tupStab E := by
    rw [hR, closure_le]
    intro r hr e he
    exact hclos e he r hr
  have heq : ∀ g ∈ K, ∀ h ∈ K, (fun i => g (v i)) = (fun i => h (v i)) → g = h := by
    intro g hg h hh he
    have h1 := hv (h⁻¹ * g) (K.mul_mem (K.inv_mem hh) hg) fun i => by
      have := congrFun he i
      rw [Equiv.Perm.mul_apply, this, Equiv.Perm.inv_eq_iff_eq]
    rw [← mul_inv_cancel_left h g, h1, mul_one]
  have hbij : Function.Bijective (fun r : R => (⟨fun i => (r : Equiv.Perm α) (v i),
      hRS r.2 v hroot⟩ : E)) := by
    constructor
    · intro r s he
      exact Subtype.ext (heq _ (hRK r.2) _ (hRK s.2) (congrArg Subtype.val he))
    · intro e
      obtain ⟨r, hr, hre⟩ := hreach e.1 e.2
      exact ⟨⟨r, hr⟩, Subtype.ext hre⟩
  refine ⟨?_, fun y hy hyE => ?_⟩
  · rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_coe]
  · obtain ⟨r, hr, hre⟩ := hreach _ hyE
    rw [heq y hy r (hRK hr) hre.symm]
    exact hr

end CFSG.KC.OrbRow

end
