module


public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Exponent

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.InvolutiveAutomorphismInvertedElement

theorem exists_cyclic_inverted {E : Type*} [Group E] (α : E ≃* E)
    (hα : ∀ y, α (α y) = y)
    (hnt : ∃ y : E, α y * y⁻¹ ∉ Subgroup.center E)
    {p : ℕ} (hp : p.Prime) (hexp : Monoid.exponent E = p) :
    ∃ x : E, x ∉ Subgroup.center E ∧ α x = x⁻¹ ∧ orderOf x = p ∧
      Nat.card (Subgroup.zpowers x) = p ∧ ¬ Subgroup.zpowers x ≤ Subgroup.center E := by
  have exists_inverted_noncentral (α : E ≃* E)
      (hα : ∀ y, α (α y) = y)
      (hnt : ∃ y : E, α y * y⁻¹ ∉ Subgroup.center E) :
      ∃ x : E, x ∉ Subgroup.center E ∧ α x = x⁻¹ := by
    obtain ⟨y, hy⟩ := hnt
    refine ⟨y * (α y)⁻¹, ?_, ?_⟩
    · intro h
      apply hy
      have := (Subgroup.center E).inv_mem h
      simpa using this
    · simp [hα]
  obtain ⟨x, hx, hax⟩ := exists_inverted_noncentral α hα hnt
  have hne : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
  have hdvd : orderOf x ∣ p := hexp ▸ Monoid.order_dvd_exponent x
  have hord : orderOf x = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  refine ⟨x, hx, hax, hord, ?_, ?_⟩
  · rw [Nat.card_zpowers, hord]
  · intro h; exact hx (h (Subgroup.mem_zpowers x))

end CFSG.GroupTheory.CoprimeActionSupport.InvolutiveAutomorphismInvertedElement
