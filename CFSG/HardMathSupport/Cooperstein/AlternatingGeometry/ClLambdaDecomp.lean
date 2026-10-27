module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace Classif

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def matchedK (ω : Perm Ω) : Subgroup (Perm Ω) :=
  Subgroup.closure {τ | ∃ x, ω x ≠ x ∧ τ = swap x (ω x)}

omit [Fintype Ω] in
theorem swap_mem_matchedK {ω : Perm Ω} {x : Ω} (hx : ω x ≠ x) : swap x (ω x) ∈ matchedK ω :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

omit [Fintype Ω] in
theorem matchedK_fix {ω : Perm Ω} (hωω : ∀ x, ω (ω x) = x) {κ : Perm Ω} (hκ : κ ∈ matchedK ω)
    {y : Ω} (hy : ω y = y) : κ y = y := by
  induction hκ using Subgroup.closure_induction with
  | mem τ hτ =>
    obtain ⟨x, hx, rfl⟩ := hτ
    refine swap_apply_of_ne_of_ne ?_ ?_
    · intro h; apply hx; rw [← h]; exact hy
    · intro h
      apply hx
      have h1 : ω y = x := by rw [h, hωω]
      have h2 : y = x := hy.symm.trans h1
      exact h.symm.trans h2
  | one => rfl
  | mul a b _ _ ha hb => rw [Perm.mul_apply, hb, ha]
  | inv a _ ha => exact Perm.inv_eq_iff_eq.2 (ha).symm

theorem exists_matchedK_eq {ω : Perm Ω} (hωω : ∀ x, ω (ω x) = x) {Sstar : Subgroup (Perm Ω)}
    (hK : ∀ x, ω x ≠ x → swap x (ω x) ∈ Sstar)
    (hfix : ∀ s ∈ Sstar, ∀ x, ω x ≠ x → s x = x ∨ s x = ω x) :
    ∀ s ∈ Sstar, ∃ κ ∈ matchedK ω, ∀ x, ω x ≠ x → κ x = s x := by
  have key : ∀ n, ∀ s ∈ Sstar, (Finset.univ.filter fun x => ω x ≠ x ∧ s x ≠ x).card = n →
      ∃ κ ∈ matchedK ω, ∀ x, ω x ≠ x → κ x = s x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro s hs hn
    by_cases h0 : ∀ x, ω x ≠ x → s x = x
    · exact ⟨1, one_mem _, fun x hx => (h0 x hx).symm ▸ rfl⟩
    · push Not at h0
      obtain ⟨x, hx, hsx⟩ := h0
      have hsx' : s x = ω x := (hfix s hs x hx).resolve_left hsx
      have hωx : ω (ω x) ≠ ω x := by rw [hωω]; exact Ne.symm hx
      have hsωx : s (ω x) = x := by
        rcases hfix s hs (ω x) hωx with h | h
        · exact absurd (s.injective (h.trans hsx'.symm)) hx
        · rw [h, hωω]
      have hs' : swap x (ω x) * s ∈ Sstar := Sstar.mul_mem (hK x hx) hs
      have hlt : (Finset.univ.filter fun y => ω y ≠ y ∧ (swap x (ω x) * s) y ≠ y).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨x, ?_, ?_⟩
          · simp [hx, hsx]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
            intro _
            rw [Perm.mul_apply, hsx', swap_apply_right]
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          refine ⟨hy.1, fun hsy => hy.2 ?_⟩
          by_cases hyx : y = x
          · subst hyx
            rw [Perm.mul_apply, hsx', swap_apply_right]
          by_cases hyωx : y = ω x
          · subst hyωx
            rw [Perm.mul_apply, hsωx, swap_apply_left]
          · rw [Perm.mul_apply, hsy, swap_apply_of_ne_of_ne hyx hyωx]
      obtain ⟨κ', hκ', hκ'eq⟩ := ih _ hlt _ hs' rfl
      refine ⟨swap x (ω x) * κ', mul_mem (swap_mem_matchedK hx) hκ', fun y hy => ?_⟩
      rw [Perm.mul_apply, hκ'eq y hy, Perm.mul_apply, swap_apply_self]
  exact fun s hs => key _ s hs rfl

@[expose] def matchedFixed (ω : Perm Ω) (Sstar : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Sstar ⊓
    { carrier := {s | ∀ x, ω x ≠ x → s x = x}
      mul_mem' := fun {a b} ha hb x hx => by rw [Perm.mul_apply, hb x hx, ha x hx]
      one_mem' := fun x _ => rfl
      inv_mem' := fun {a} ha x hx => Perm.inv_eq_iff_eq.2 (ha x hx).symm }

omit [Fintype Ω] [DecidableEq Ω] in
theorem mem_matchedFixed {ω : Perm Ω} {Sstar : Subgroup (Perm Ω)} {s : Perm Ω} :
    s ∈ matchedFixed ω Sstar ↔ s ∈ Sstar ∧ ∀ x, ω x ≠ x → s x = x := Iff.rfl

theorem eq_matchedK_mul {ω : Perm Ω} (hωω : ∀ x, ω (ω x) = x) {Sstar : Subgroup (Perm Ω)}
    (hK : ∀ x, ω x ≠ x → swap x (ω x) ∈ Sstar)
    (hfix : ∀ s ∈ Sstar, ∀ x, ω x ≠ x → s x = x ∨ s x = ω x) {s : Perm Ω} (hs : s ∈ Sstar) :
    ∃ κ ∈ matchedK ω, ∃ p ∈ matchedFixed ω Sstar, s = κ * p := by
  obtain ⟨κ, hκ, hκeq⟩ := exists_matchedK_eq hωω hK hfix s hs
  have hKS : matchedK ω ≤ Sstar := by
    refine (Subgroup.closure_le Sstar).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hK x hx
  refine ⟨κ, hκ, κ⁻¹ * s, ⟨Sstar.mul_mem (Sstar.inv_mem (hKS hκ)) hs, fun x hx => ?_⟩, by simp⟩
  rw [Perm.mul_apply, ← hκeq x hx]
  simp

end Classif

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
